#include "ffta.h"

typedef struct {
    u16 current;
    u16 count;
    u16 entries[34];
    u8  unknown_48[5];
    u8  unknown_4d;
    u8  unknown_4e[3];
    u8  unknown_51;
    u8  unknown_52[10];
    u32 unknown_5c;
} ScriptState;

typedef struct {
    u32 unknown_00;
    u32 field_04;
    u16 unknown_08;
    u16 unknown_0a;
    u16 field_0c;
} Record;

void func_08064004(void)
{
    u16 *rec = (u16 *)0x020020D0;
    ScriptState *state = *(ScriptState **)0x0200F450;

    rec[2] = state->unknown_5c;
    rec[6] = 0x11;
    state->unknown_4d = 0x0B;
    state->unknown_51 = 0x90;
    state->entries[state->count++] = state->current;
    state->current = 0x26;
    state->entries[state->count++] = state->current;
    state->current = 0x37;
    state->entries[state->count++] = state->current;
    state->current = 0x31;
}
