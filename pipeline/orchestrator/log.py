"""Per-run JSONL event log (`runs/<crate>/<arm>/<timestamp>/events.jsonl`)."""

from __future__ import annotations

import json
import time
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any


@dataclass
class EventLog:
    path: Path

    def __post_init__(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)

    def emit(self, event: str, **fields: Any) -> None:
        record = {"ts": datetime.now(UTC).isoformat(timespec="milliseconds"), "t": round(time.time(), 3),
                  "event": event, **fields}
        with open(self.path, "a") as f:
            f.write(json.dumps(record, sort_keys=True) + "\n")

    def read(self) -> list[dict[str, Any]]:
        if not self.path.is_file():
            return []
        return [json.loads(line) for line in self.path.read_text().splitlines() if line.strip()]
