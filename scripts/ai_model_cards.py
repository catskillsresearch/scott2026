"""Model-card registry for the AI-assisted development acknowledgements block.

Injected into `arxiv_with_code.md` / `arxiv.tex` by `build_arxiv_tex.py` at:
  <!-- AI_MODEL_TOOL_BULLETS --> … <!-- /AI_MODEL_TOOL_BULLETS -->
  <!-- AI_MODEL_REFERENCES --> … <!-- /AI_MODEL_REFERENCES -->
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    reference: str


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="GPT-5.6",
        cite_key="Gpt26",
        tool_note=(
            "OpenAI's GPT-5.6 family in Cursor (Sol variant) for Lean 4 / mathlib "
            "formalization, `lake build` repair, and long-running agent loops on "
            "`Scott2026/`. Generated Lean was provisional until it compiled under the "
            "pinned toolchain."
        ),
        reference=(
            "OpenAI. *GPT-5.6* (Sol variant as integrated in Cursor). Model documentation, "
            "<https://cursor.com/docs/models/gpt-5-6-sol> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude Fable 5",
        cite_key="Fab26",
        tool_note=(
            "selective use in Cursor for the heaviest proof work and long-horizon "
            "formalization. Every emitted proof term was checked by the Lean kernel."
        ),
        reference=(
            "Anthropic. *Claude Fable 5*. Announcement, "
            "<https://www.anthropic.com/news/claude-fable-5-mythos-5>; system card, "
            "<https://www-cdn.anthropic.com/2f9323abbcc4abe219577539efe19a623c9ca2bd/"
            "Claude%20Fable%205%20&%20Claude%20Mythos%205%20System%20Card.pdf>; "
            "Cursor model page, <https://cursor.com/docs/models/claude-fable-5> "
            "(accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude Opus 5",
        cite_key="Opu26",
        tool_note=(
            "day-to-day formalization and proof-engineering in Cursor: inventory and "
            "narrative maintenance, module wiring, and medium-to-hard Lean obligations "
            "where the proof strategy was already fixed."
        ),
        reference=(
            "Anthropic. *Claude Opus 5*. Announcement, "
            "<https://www.anthropic.com/research/claude-opus-5>; model documentation as "
            "integrated in Cursor, <https://cursor.com/docs/models/claude-opus-5> "
            "(accessed 2026)."
        ),
    ),
    ModelCard(
        label="Cursor Grok 4.6",
        cite_key="Grk26",
        tool_note=(
            "primary SpaceXAI / Cursor agent for Lean 4 / mathlib formalization, "
            "`lake build` repair, vision-OCR transcription, drafting this narrative "
            "(`arxiv.md`), and tracking the formalized inventory."
        ),
        reference=(
            "SpaceXAI and Anysphere, Inc. *Grok 4.6*. Official model card, "
            "<https://media.x.ai/v1/website/card-7f81d41b.pdf>; developer documentation, "
            "<https://docs.x.ai/developers/models/grok-4.6>; Cursor model page, "
            "<https://cursor.com/docs/models/grok-4-6>; Cursor announcement, "
            "<https://cursor.com/blog/grok-4-6> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Cursor Composer 2.5",
        cite_key="Cmp25",
        tool_note=(
            "routine multi-step work: module scaffolding, dependency-ordered wiring of "
            "`Scott2026/`, documentation, and medium proof obligations where the "
            "strategy was already fixed."
        ),
        reference=(
            "Anysphere, Inc. *Composer 2.5*. Model announcement and documentation, "
            "<https://cursor.com/blog/composer-2-5>; model card as integrated in Cursor, "
            "<https://cursor.com/docs/models/composer-2-5> (accessed 2026)."
        ),
    ),
)

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** **[{card.cite_key}]** — {card.tool_note}" for card in MODEL_CARDS
    )


def render_model_references() -> str:
    return "\n".join(f"- **[{card.cite_key}]** {card.reference}" for card in MODEL_CARDS)


def inject_model_cards(text: str) -> str:
    """Expand acknowledgement markers; pass through unchanged if markers absent."""
    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} in narrative; add markers to arxiv.md Acknowledgments"
        )
    if REFERENCES_BEGIN not in text:
        raise RuntimeError(
            f"missing {REFERENCES_BEGIN} in narrative; add markers to arxiv.md References"
        )

    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, render_model_references())
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    # Preserve one leading newline after begin marker when present.
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
