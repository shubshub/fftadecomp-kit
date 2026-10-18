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
    Record *rec = (Record *)0x020020D0;
    u8 *state = *(u8 **)0x0200F450;

    rec->field_04 = *(u32 *)(state + 0x5c);
    rec->field_0c = 0x11;
    state[0x4d] = 0x0B;
    state[0x51] = 0x90;
    *(u16 *)(state + 0) = *(u16 *)(state + 0);
    ((ScriptState *)state)->entries[((ScriptState *)state)->count++] = ((ScriptState *)state)->current;
    ((ScriptState *)state)->current = 0x26;
    ((ScriptState *)state)->entries[((ScriptState *)state)->count++] = ((ScriptState *)state)->current;
    ((ScriptState *)state)->current = 0x37;
    ((ScriptState *)state)->entries[((ScriptState *)state)->count++] = ((ScriptState *)state)->current;
    ((ScriptState *)state)->current = 0x31;
}
