"""Embeddings of canonical definition text.

The pinned local code-embedding model (config `retrieval.embedding_model`) is
used through `sentence-transformers` when it is installed and the model is
available offline. Otherwise a deterministic hashed character-n-gram embedding
(`hashed-ngram`) is used; the choice is recorded in every run's metadata so
that arms are never compared across embedders.
"""

from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass, field
from typing import Any

import numpy as np


def hashed_ngram_embedding(text: str, dim: int = 512, ns: tuple[int, ...] = (3, 4, 5)) -> np.ndarray:
    vec = np.zeros(dim, dtype=np.float32)
    toks = " ".join(text.split())
    for n in ns:
        for i in range(max(0, len(toks) - n + 1)):
            g = toks[i:i + n]
            h = int.from_bytes(hashlib.blake2b(g.encode(), digest_size=8).digest(), "little")
            vec[h % dim] += 1.0 if (h >> 63) == 0 else -1.0
    norm = np.linalg.norm(vec)
    return vec / norm if norm > 0 else vec


@dataclass
class Embedder:
    model_name: str
    backend: str = "hashed-ngram"
    _model: Any = field(default=None, repr=False)
    calls: int = 0

    @staticmethod
    def create(model_name: str, allow_download: bool = False) -> Embedder:
        try:
            if not allow_download:
                os.environ.setdefault("HF_HUB_OFFLINE", "1")
                os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
            from sentence_transformers import SentenceTransformer  # type: ignore

            model = SentenceTransformer(model_name, trust_remote_code=True)
            return Embedder(model_name=model_name, backend="sentence-transformers", _model=model)
        except Exception:
            return Embedder(model_name=model_name, backend="hashed-ngram")

    def embed(self, text: str) -> np.ndarray:
        self.calls += 1
        if self._model is not None:
            v = np.asarray(self._model.encode(text, normalize_embeddings=True), dtype=np.float32)
            return v
        return hashed_ngram_embedding(text)

    @property
    def descriptor(self) -> str:
        return f"{self.backend}:{self.model_name}" if self.backend != "hashed-ngram" else "hashed-ngram:blake2b-512"


def cosine(a: np.ndarray, b: np.ndarray) -> float:
    na, nb = np.linalg.norm(a), np.linalg.norm(b)
    if na == 0 or nb == 0:
        return 0.0
    return float(np.dot(a, b) / (na * nb))
