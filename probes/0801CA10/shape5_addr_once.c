/* shape candidates for 0x0801CA10.
 *
 * All do the same thing - scale three s16 by 32/16/32 through a local s16[3]
 * and write the low bytes out.  They differ only in the code-generation shape:
 * how the addresses of scaled[k] get materialised, and what type the temporaries
 * are.  The ROM keeps &scaled[0..2] in registers; the straightforward form
 * folds them into one sp base plus immediates.
 *
 * Run:  python tools/probe.py 0x0801CA10 --dir probes/0801CA10 --dumps
 */

#include "ffta.h"

#define BODY(T)                                                          \
    scaled[0] = first >> 5;                                              \
    scaled[1] = second >> 4;                                             \
    scaled[2] = third >> 5;                                              \
    destination[0] = scaled[0];                                          \
    destination[1] = scaled[1];                                          \
    destination[2] = scaled[2];

#define SETUP(T)                                                         \
    T first = source[0], second = source[1], third = source[2];

void shape5_addr_once(s16 *source, u8 *destination) {
    s16 scaled[3];
    s16 *p0 = scaled, *p1 = scaled + 1, *p2 = scaled + 2;
    SETUP(s32)
    *p0 = first >> 5;
    *p1 = second >> 4;
    *p2 = third >> 5;
    destination[0] = scaled[0];
    destination[1] = scaled[1];
    destination[2] = scaled[2];
}

