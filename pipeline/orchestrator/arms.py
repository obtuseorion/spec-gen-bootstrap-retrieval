"""Ablation arms (IMPLEMENTATION.md §7 / design §6).

| arm | examples |
|---|---|
| A | none |
| B | external corpus only (hand-curated Aeneas examples) |
| C | bootstrapped, similarity-selected (the proposal) |
| D | bootstrapped, random in-crate examples at the same count |
| E | C with the external corpus added to the candidate set |
| F | bootstrapped, structural filter + Jaccard ranking (no embeddings) |
"""

from __future__ import annotations

from dataclasses import dataclass

ARMS = ("A", "B", "C", "D", "E", "F")


@dataclass(frozen=True)
class Arm:
    name: str

    def __post_init__(self) -> None:
        if self.name not in ARMS:
            raise ValueError(f"unknown arm {self.name!r}; expected one of {ARMS}")

    @property
    def uses_examples(self) -> bool:
        return self.name != "A"

    @property
    def uses_external(self) -> bool:
        return self.name in ("B", "E")

    @property
    def uses_embeddings(self) -> bool:
        return self.name in ("C", "E")

    @property
    def random_examples(self) -> bool:
        return self.name == "D"

    @property
    def description(self) -> str:
        return {
            "A": "no examples", "B": "external curated examples", "C": "bootstrapped similarity-selected",
            "D": "bootstrapped random", "E": "bootstrapped similarity + external", "F": "bootstrapped Jaccard-ranked",
        }[self.name]
