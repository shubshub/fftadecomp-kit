#include "ffta.h"

typedef struct {
    u8 unknown_00;
    u8 kind;
} ActionRecord;

typedef struct {
    void *source;
    void *target;
    u8 unknown_08[0x1E];
    u16 flags;
    u8 unknown_28[8];
    const ActionRecord *record;
} ActionState;

extern ActionState data_0200F3F0;
extern s32 func_0812E0BC(const void *source, const void *target, u16 item,
                         u8 mode, u32 flags);
extern s32 func_08130200(void *source, void *target, u16 action,
                         u16 equipment, u16 attribute, u16 mode);
extern u8 func_080C8280(const void *object);
extern s32 func_080C7EA4(const void *object, u32 selector);
extern u32 func_080CCD50(u16 index, u8 selector);
extern void func_0812F2A4(u16 first, u16 second, u8 kind);
extern void func_0812F328(u8 index);
extern void func_0812F34C(u32 value);
extern u8 func_0812F358(void);
extern void func_0812F39C(s32 index);
extern u8 func_08130FBC(void);
extern u8 func_08131378(void);
extern s32 func_08131B20(void);
extern s32 func_08133988(void);

/* Complete [0x080C2314, 0x080C2616): 770 bytes, 385 instructions,
 * including the six-entry jump table at 0x080C24F8.
 *
 * chance holds a hit chance: first the one func_0812E0BC returns for the
 * whole action, then, inside the loop, the one func_08131378 returns for
 * each of the action's three effects (both return 100 for the same target
 * test).  The ROM keeps the two in one register, r6.
 */
u8 func_080C2314(void *source, void *target, u16 action, u16 equipment,
                 u16 *kinds, s16 *total, s16 *raw, u8 *flags, u16 mode)
{
    ActionState *state;
    s32 count;
    s16 base_chance;
    s16 chance;
    s16 value;
    s32 remaining;
    s32 index;
    u8 critical;
    s16 amount;

    *total = 0;
    *raw = 0;
    chance = func_0812E0BC(source, target, action, 1, mode);
    value = func_08130200(source, target, action, equipment, 0, 2);
    base_chance = chance;
    if (chance == 0)
        chance = 1;
    state = &data_0200F3F0;

    if (action == 0) {
        if (target == source || func_080C8280(target))
            return 0;
        *raw = value;
        remaining = func_080C7EA4(target, 0x13);
        remaining -= value;
        if ((u32)remaining > (u32)func_080C7EA4(target, 0x14))
            value = func_080C7EA4(target, 0x14) - func_080C7EA4(target, 0x13);
        if (remaining < 0)
            value = func_080C7EA4(target, 0x13);
        if (value == 0)
            return 0;
        if (value > 0) {
            *kinds = 0x15;
            value += chance;
            *raw += chance;
        } else {
            *kinds = 0x26;
            value -= chance;
            *raw -= chance;
        }
        *total = value;
        return 1;
    }

    if ((func_080CCD50(action, 11) == 0 && source == target)
        || (action == 0x109 && source != target))
        return 0;

    func_0812F2A4(action, equipment, 0);
    state->source = source;
    state->target = target;
    critical = 0;
    state->flags |= 0x10;
    count = 0;
    for (index = 0; index < 3; index++) {
        func_0812F328(index);
        func_0812F34C(0);
        if (!func_08130FBC())
            continue;
        chance = func_08131378();
        value = func_08131B20();
        if (chance <= 3)
            chance = 1;
        *raw += value;
        func_0812F39C(index);
        func_0812F34C((u32)target);
        kinds[count] = state->record->kind;
        amount = chance;
        if (func_08133988() < 0)
            amount = -chance;
        /* Cases 3 to 6 have separate, identical bodies: the ROM dispatches
         * them through the jump table (0x080C24F8, entries 3 to 6 all
         * 0x080C2554), where one label for all four compiles to a range
         * test instead; cross-jumping leaves one copy at 0x080C2554. */
        switch (func_0812F358()) {
        case 1:
            if (value < 0) {
                amount = -chance;
                kinds[count] = 0x26;
            }
            if (value > 0) {
                kinds[count] = 0x15;
                amount = chance;
            }
            break;
        case 2:
            if (value < 0) {
                kinds[count] = 9;
                amount = -chance;
            }
            if (value > 0) {
                kinds[count] = 8;
                amount = chance;
            }
            break;
        case 3:
            if (value < 0)
                amount = -chance;
            if (value > 0)
                amount = chance;
            break;
        case 4:
            if (value < 0)
                amount = -chance;
            if (value > 0)
                amount = chance;
            break;
        case 5:
            if (value < 0)
                amount = -chance;
            if (value > 0)
                amount = chance;
            break;
        case 6:
            if (value < 0)
                amount = -chance;
            if (value > 0)
                amount = chance;
            break;
        default:
            value = 0;
            if (func_08133988() > 0)
                critical = func_08133988();
            break;
        }
        *total += value + amount;
        *raw += amount;
        if (chance != 0)
            count++;
    }

    if (critical && *total < 0)
        *flags |= 1;
    if (base_chance == 0 && *total <= 0)
        count = 0;
    if (action == 0x146) {
        *total = 100;
        *raw = 100;
        if (count == 0) {
            *kinds = 0x51;
            count = 1;
        }
    }
    return count;
}
