"""Configuration: `pipeline/config.toml` with paths resolved against the repository root."""

from __future__ import annotations

import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class Config:
    raw: dict[str, Any]
    root: Path = REPO_ROOT

    # ---- paths ------------------------------------------------------------
    def path(self, key: str) -> Path:
        value = self.raw["paths"][key]
        p = Path(value)
        return p if p.is_absolute() else self.root / p

    @property
    def project(self) -> Path:
        return self.path("project")

    @property
    def namespace(self) -> str:
        return self.raw["paths"]["project_namespace"]

    @property
    def lean_tools(self) -> Path:
        return self.path("lean_tools")

    @property
    def corpus_store(self) -> Path:
        return self.path("corpus_store")

    @property
    def runs(self) -> Path:
        return self.path("runs")

    @property
    def prompts(self) -> Path:
        return self.path("prompts")

    @property
    def external_corpus(self) -> Path | None:
        v = self.raw["paths"].get("external_corpus", "")
        if not v:
            return None
        p = Path(v)
        return p if p.is_absolute() else self.root / p

    # ---- sections ---------------------------------------------------------
    @property
    def budgets(self) -> dict[str, Any]:
        return self.raw["budgets"]

    @property
    def gate(self) -> dict[str, Any]:
        return self.raw["gate"]

    @property
    def retrieval(self) -> dict[str, Any]:
        return self.raw["retrieval"]

    @property
    def llm(self) -> dict[str, Any]:
        return self.raw["llm"]

    @property
    def toolchain(self) -> dict[str, Any]:
        return self.raw.get("toolchain", {})


def load_config(path: Path | None = None) -> Config:
    path = path or REPO_ROOT / "pipeline/config.toml"
    with open(path, "rb") as f:
        raw = tomllib.load(f)
    return Config(raw=raw, root=path.resolve().parents[1])
