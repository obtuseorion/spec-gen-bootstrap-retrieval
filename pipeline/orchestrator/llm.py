"""LLM client (IMPLEMENTATION.md Task 8): one function `complete(prompt, max_tokens) -> (text, usage)`.

* `AnthropicLLM` — the Anthropic SDK (model pinned in config; adaptive thinking, streaming,
  server-side refusal fallbacks enabled, SDK retries for transient failures).
* `FakeLLM` — canned responses from `tests/fixtures/fake_llm/<unit>/…` for dry runs;
  anything without a fixture gets a response with no ```lean block (which counts as an attempt).

`extract_lean_block` returns the single ```lean block of a response, or `None` when the
response has zero or several blocks — both are rejected and counted as an attempt.
"""

from __future__ import annotations

import re
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol

_LEAN_BLOCK = re.compile(r"```lean[^\n]*\n(.*?)```", re.DOTALL)


@dataclass
class Usage:
    input_tokens: int = 0
    output_tokens: int = 0
    calls: int = 0
    elapsed_s: float = 0.0

    def to_json(self) -> dict[str, Any]:
        return self.__dict__.copy()


def extract_lean_block(text: str) -> str | None:
    blocks = _LEAN_BLOCK.findall(text)
    if len(blocks) != 1:
        return None
    return blocks[0].strip("\n")


class LLM(Protocol):
    name: str

    def complete(self, prompt: str, max_tokens: int, effort: str | None = None) -> tuple[str, Usage]: ...


@dataclass
class AnthropicLLM:
    model: str = "claude-opus-5"
    temperature: float | None = None
    name: str = "anthropic"
    effort: str = "medium"          # output_config.effort for the call (adaptive thinking on)
    retry_effort: str = "low"       # used once when a call returns no text (thinking exhausted max_tokens)
    _client: Any = field(default=None, repr=False)

    def __post_init__(self) -> None:
        import anthropic  # optional dependency, imported lazily

        self._client = anthropic.Anthropic(max_retries=4)

    def _call(self, prompt: str, max_tokens: int, effort: str) -> Any:
        kwargs: dict[str, Any] = dict(
            model=self.model,
            max_tokens=max_tokens,
            messages=[{"role": "user", "content": prompt}],
            output_config={"effort": effort},
            # server-side refusal fallbacks: a policy decline re-runs the request on a fallback model
            betas=["server-side-fallback-2026-07-01"],
            fallbacks="default",
        )
        try:
            with self._client.beta.messages.stream(**kwargs) as stream:
                return stream.get_final_message()
        except TypeError:
            # SDK without the server-side fallback parameter: plain request
            kwargs.pop("betas", None)
            kwargs.pop("fallbacks", None)
            with self._client.messages.stream(**kwargs) as stream:
                return stream.get_final_message()

    def complete(self, prompt: str, max_tokens: int, effort: str | None = None) -> tuple[str, Usage]:
        t0 = time.monotonic()
        effort = effort or self.effort
        message = self._call(prompt, max_tokens, effort)
        usage = Usage(input_tokens=message.usage.input_tokens, output_tokens=message.usage.output_tokens, calls=1)
        text = "".join(block.text for block in message.content if block.type == "text")
        if not text.strip() and message.stop_reason == "max_tokens" and self.retry_effort != effort:
            # thinking consumed the whole budget: one retry at lower effort
            message = self._call(prompt, max_tokens, self.retry_effort)
            usage.input_tokens += message.usage.input_tokens
            usage.output_tokens += message.usage.output_tokens
            usage.calls += 1
            text = "".join(block.text for block in message.content if block.type == "text")
        usage.elapsed_s = round(time.monotonic() - t0, 3)
        if message.stop_reason == "refusal":
            text = ""
        return text, usage


@dataclass
class FakeLLM:
    """Canned responses keyed by (unit, stage, member) from a fixtures directory.

    Layout: `<fixtures>/<unit id>/spec.<member>.lean` and `proof.<member>.lean`; the
    orchestrator sets `context` before each call so the fake knows what is being asked.
    """
    fixtures: Path
    name: str = "fake"
    context: dict[str, str] = field(default_factory=dict)
    calls: int = 0

    def complete(self, prompt: str, max_tokens: int, effort: str | None = None) -> tuple[str, Usage]:
        self.calls += 1
        unit, stage, member = self.context.get("unit", ""), self.context.get("stage", ""), self.context.get("member", "")
        attempt = int(self.context.get("attempt", "1"))
        candidates = [self.fixtures / unit / f"{stage}.{member}.{attempt}.lean", self.fixtures / unit / f"{stage}.{member}.lean"]
        for f in candidates:
            if f.is_file():
                return "```lean\n" + f.read_text().strip("\n") + "\n```\n", Usage(input_tokens=len(prompt) // 4, output_tokens=64, calls=1)
        return "I do not have a canned answer for this unit.", Usage(input_tokens=len(prompt) // 4, output_tokens=8, calls=1)


def make_llm(kind: str, config: dict[str, Any], fixtures: Path | None = None) -> LLM:
    if kind == "fake":
        return FakeLLM(fixtures=fixtures or Path("tests/fixtures/fake_llm"))
    if kind == "anthropic":
        return AnthropicLLM(model=config.get("model", "claude-opus-5"), effort=str(config.get("effort", "medium")),
                            retry_effort=str(config.get("retry_effort", "low")))
    raise ValueError(f"unknown llm kind {kind!r}")
