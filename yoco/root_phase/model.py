from __future__ import annotations
import math
from dataclasses import asdict, dataclass
from typing import Any
import torch
from torch import nn
from torch.nn import functional as F
from .data import FEATURE_DIM, HOP_DEPTH, MAX_CUT_SIZE

@dataclass
class RootPhaseDetrConfig:
    input_dim: int = FEATURE_DIM
    gcn_hidden: int = 128
    gcn_layers: int = 4
    d_model: int = 256
    nhead: int = 8
    encoder_layers: int = 4
    decoder_layers: int = 4
    dim_feedforward: int = 1024
    dropout: float = 0.1
    max_hop: int = HOP_DEPTH
    max_cut_size: int = MAX_CUT_SIZE

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> 'RootPhaseDetrConfig':
        return cls(**data)

class SignedGraphConv(nn.Module):

    def __init__(self, dim: int, dropout: float) -> None:
        super().__init__()
        self.self_lin = nn.Linear(dim, dim)
        self.pos_lin = nn.Linear(dim, dim, bias=False)
        self.neg_lin = nn.Linear(dim, dim, bias=False)
        self.norm = nn.LayerNorm(dim)
        self.dropout = nn.Dropout(dropout)

    def forward(self, x: torch.Tensor, edge_index: torch.Tensor, edge_inv: torch.Tensor) -> torch.Tensor:
        residual = x
        out = self.self_lin(x)
        if edge_index.numel() > 0:
            src, dst = (edge_index[0], edge_index[1])
            msg_pos = self.pos_lin(x[src])
            msg_neg = self.neg_lin(x[src])
            inv = edge_inv.to(dtype=torch.bool).unsqueeze(-1)
            msg = torch.where(inv, msg_neg, msg_pos)
            agg = torch.zeros_like(out)
            agg.index_add_(0, dst, msg)
            deg = torch.zeros((x.shape[0],), device=x.device, dtype=x.dtype)
            deg.index_add_(0, dst, torch.ones_like(dst, dtype=x.dtype))
            out = out + agg / deg.clamp_min(1.0).unsqueeze(-1)
        out = self.norm(residual + self.dropout(F.gelu(out)))
        return out

class RootPhaseDETR(nn.Module):

    def __init__(self, config: RootPhaseDetrConfig | None=None) -> None:
        super().__init__()
        self.config = config or RootPhaseDetrConfig()
        c = self.config
        self.input_proj = nn.Linear(c.input_dim, c.gcn_hidden)
        self.gcn = nn.ModuleList([SignedGraphConv(c.gcn_hidden, c.dropout) for _ in range(c.gcn_layers)])
        self.gcn_to_model = nn.Linear(c.gcn_hidden, c.d_model)
        self.hop_embedding = nn.Embedding(c.max_hop + 1, c.d_model)
        enc_layer = nn.TransformerEncoderLayer(d_model=c.d_model, nhead=c.nhead, dim_feedforward=c.dim_feedforward, dropout=c.dropout, activation='gelu', batch_first=True, norm_first=True)
        self.encoder = nn.TransformerEncoder(enc_layer, num_layers=c.encoder_layers, norm=nn.LayerNorm(c.d_model))
        dec_layer = nn.TransformerDecoderLayer(d_model=c.d_model, nhead=c.nhead, dim_feedforward=c.dim_feedforward, dropout=c.dropout, activation='gelu', batch_first=True, norm_first=True)
        self.decoder = nn.TransformerDecoder(dec_layer, num_layers=c.decoder_layers, norm=nn.LayerNorm(c.d_model))
        self.phase_embedding = nn.Embedding(2, c.d_model)
        self.query_norm = nn.LayerNorm(c.d_model)
        self.select_head = nn.Linear(c.d_model, 2)
        self.leaf_key = nn.Linear(c.d_model, c.d_model, bias=False)
        self.leaf_query = nn.ModuleList([nn.Linear(c.d_model, c.d_model, bias=False) for _ in range(c.max_cut_size)])
        self.null_key = nn.Parameter(torch.empty(c.max_cut_size, c.d_model))
        self.null_bias = nn.Parameter(torch.zeros(c.max_cut_size))
        self.reset_parameters()

    def reset_parameters(self) -> None:
        nn.init.normal_(self.phase_embedding.weight, std=0.02)
        nn.init.normal_(self.null_key, std=0.02)

    def forward(self, batch: dict[str, torch.Tensor]) -> dict[str, Any]:
        x = batch['x']
        hop = batch['hop']
        node_mask = batch['node_mask']
        edge_index = batch['edge_index']
        edge_inv = batch['edge_inv']
        bsz, n_nodes, _ = x.shape
        h = self.input_proj(x).reshape(bsz * n_nodes, -1)
        for layer in self.gcn:
            h = layer(h, edge_index, edge_inv)
        h = self.gcn_to_model(h).reshape(bsz, n_nodes, -1)
        h = h + self.hop_embedding(hop.clamp(0, self.config.max_hop))
        memory = self.encoder(h, src_key_padding_mask=~node_mask)
        root_h = memory[:, 0, :]
        phase_ids = torch.arange(2, device=x.device, dtype=torch.long)
        queries = root_h.unsqueeze(1) + self.phase_embedding(phase_ids).unsqueeze(0)
        queries = self.query_norm(queries)
        decoded = self.decoder(tgt=queries, memory=memory, memory_key_padding_mask=~node_mask)
        select_logits = self.select_head(decoded)
        keys = self.leaf_key(memory)
        leaf_logits: list[torch.Tensor] = []
        scale = math.sqrt(float(self.config.d_model))
        for slot in range(self.config.max_cut_size):
            q = self.leaf_query[slot](decoded)
            score = torch.einsum('bqd,bnd->bqn', q, keys) / scale
            score = score.masked_fill(~node_mask.unsqueeze(1), torch.finfo(score.dtype).min)
            null = torch.einsum('bqd,d->bq', q, self.null_key[slot]) / scale + self.null_bias[slot]
            leaf_logits.append(torch.cat([score, null.unsqueeze(-1)], dim=-1))
        return {'select_logits': select_logits, 'leaf_logits': leaf_logits, 'memory': memory, 'decoded': decoded}
