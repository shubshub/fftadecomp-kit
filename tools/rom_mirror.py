"""The Game Pak ROM's wait-state mirrors.

The GBA maps the cartridge ROM three times: at 0x08000000-0x09FFFFFF (wait
state 0), 0x0A000000-0x0BFFFFFF (wait state 1) and 0x0C000000-0x0DFFFFFF (wait
state 2). Only the access timing differs, so a mirror word names the same ROM
byte, code or data, as its wait-state-0 address. Every rule that classes a
value as ROM, as code, or as an address that needs typed provenance compares
the folded value. 0x0E000000-0x0FFFFFFF is the SRAM/flash bus, not ROM, and
is never folded.
"""

MIRRORS = (0x0A000000, 0x0E000000)
# The owner rule's typed address domain: RAM, I/O to OAM, and the ROM image.
TYPED_DOMAIN = (0x02000000, 0x09000000)


def mirror(value):
    """True for a word in either ROM wait-state mirror."""
    return MIRRORS[0] <= value < MIRRORS[1]


def canonical(value):
    """The wait-state-0 address a ROM mirror word names; any other value unchanged."""
    return value & ~0x06000000 if mirror(value) else value


def typed_domain(value):
    """True for a word in the typed address domain once a ROM mirror is folded."""
    return TYPED_DOMAIN[0] <= canonical(value) < TYPED_DOMAIN[1]
