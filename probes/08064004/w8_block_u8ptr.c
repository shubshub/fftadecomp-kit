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

    rec->field_04 = (*(ScriptState **)0x0200F450)->unknown_5c;
    rec->field_0c = 0x11;
    (*(ScriptState **)0x0200F450)->unknown_4d = 0x0B;
    (*(ScriptState **)0x0200F450)->unknown_51 = 0x90;
    {
        u8 *st = (u8 *)(*(ScriptState **)0x0200F450);

        *(u16 *)(st + *(u16 *)(st + 2) * 2 + 4) = *(u16 *)st;
        *(u16 *)(st + 2) += 1;
        *(u16 *)st = 0x26;
        *(u16 *)(st + *(u16 *)(st + 2) * 2 + 4) = *(u16 *)st;
        *(u16 *)(st + 2) += 1;
        *(u16 *)st = 0x37;
        *(u16 *)(st + *(u16 *)(st + 2) * 2 + 4) = *(u16 *)st;
        *(u16 *)(st + 2) += 1;
        *(u16 *)st = 0x31;
    }
}
