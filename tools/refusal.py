"""The refusal type: a selector or profile declining a source."""


class Refusal(ValueError):
    """Subclass of ValueError, so existing handlers and tests still catch it;
    match.py run as a script reports it as 'refused: <reason>'."""
