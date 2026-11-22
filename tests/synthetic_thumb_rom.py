"""Synthetic Thumb ROM images for the callee-interface tests, never copied from a game ROM."""

BASE = 0x08000000


def image(functions, size):
    """A ROM image of `size` bytes from 0x08000000 holding `functions`, and its function index.

    Each function is (address, halfwords): the halfwords are written from the
    address on, and an entry ("bl", target) is the two-halfword BL to target.
    The index has one Thumb row per function, in order and without an end.
    """
    rom = bytearray(size)
    for address, words in functions:
        position = address - BASE
        for word in words:
            if isinstance(word, tuple):
                offset = word[1] - (BASE + position + 4)
                halves = (0xF000 | ((offset >> 12) & 0x7FF), 0xF800 | ((offset >> 1) & 0x7FF))
            else:
                halves = (word,)
            for half in halves:
                rom[position:position + 2] = half.to_bytes(2, "little")
                position += 2
    return bytes(rom), [{"rom": f"0x{address:08X}", "mode": "thumb"} for address, _ in functions]
