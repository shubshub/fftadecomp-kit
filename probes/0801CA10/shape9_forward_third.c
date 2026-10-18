/* shape candidates for 0x0801CA10, part 2.
 *
 * The table from probe.py says the straightforward shapes all land at 52 bytes
 * with two stack addresses in registers, while the ROM wants three
 * (mov r0,sp / mov r6,sp+adds r6,#2 / add r5,sp,#4) and is two bytes longer.
 * Every shape that forces the extra materialisation pays for it in spill
 * traffic, so these try to get the third address without paying: ordering,
 * declaration order, forwarding the value instead of reloading it, and letting
 * the compiler see fewer aliases.
 */

#include "ffta.h"

void shape9_forward_third(s16 *source, u8 *destination) {
    s32 first, second, third;
    s16 scaled[3];
    first = source[0]; second = source[1]; third = source[2];
    scaled[0] = first >> 5;
    scaled[1] = second >> 4;
    scaled[2] = third >> 5;
    destination[0] = scaled[0];
    destination[1] = scaled[1];
    destination[2] = third >> 5;
}

