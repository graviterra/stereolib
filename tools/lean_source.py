"""Scan Lean import headers without interpreting declaration bodies."""

from __future__ import annotations

import re

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def _next_token(text: str, offset: int) -> tuple[str, int]:
    """Read one header token, skipping whitespace and nested comments."""
    while offset < len(text):
        if text[offset].isspace():
            offset += 1
        elif text.startswith("--", offset):
            end = text.find("\n", offset)
            offset = len(text) if end == -1 else end + 1
        elif text.startswith("/-", offset):
            offset += 2
            depth = 1
            while depth:
                if offset >= len(text):
                    raise ValueError("Unterminated Lean comment")
                if text.startswith("/-", offset):
                    depth += 1
                    offset += 2
                elif text.startswith("-/", offset):
                    depth -= 1
                    offset += 2
                else:
                    offset += 1
        else:
            break
    start = offset
    while offset < len(text) and not text[offset].isspace():
        if text.startswith(("/-", "--"), offset):
            break
        offset += 1
    return text[start:offset], offset



def imports(text: str) -> list[str]:
    """Return header imports; reject module names outside the supported ASCII grammar."""
    token, offset = _next_token(text, 0)
    for optional in ("module", "prelude"):
        if token == optional:
            token, offset = _next_token(text, offset)
    result: list[str] = []
    # Match the installed Module.header grammar, stopping at the first body command.
    while True:
        for optional in ("public", "meta"):
            if token == optional:
                token, offset = _next_token(text, offset)
        if token != "import":
            return result
        token, offset = _next_token(text, offset)
        if token == "all":
            token, offset = _next_token(text, offset)
        if IDENT.fullmatch(token) is None:
            raise ValueError(
                "Unsupported Lean import identifier; quoted/Unicode/partial names require explicit support"
            )
        result.append(token)
        token, offset = _next_token(text, offset)
