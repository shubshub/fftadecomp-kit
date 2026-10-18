typedef unsigned char  u8;
typedef signed char    s8;
typedef unsigned short u16;
typedef signed short   s16;
typedef unsigned int   u32;
typedef signed int     s32;

void func_0801C984(s16 first, s16 second, s16 third, s16 *firstOutput,
                   s16 *secondOutput)
{
    s16 scaled[3];
    s16 *low;
    s16 *mid;
    s16 *high;
    s16 *origin;
    s32 a, b;

    origin = (s16 *)0x02007F40;
    low = &scaled[0];
    mid = &scaled[1];
    high = &scaled[2];
    *low = ((first - third) >> 1) + origin[0x10];
    *mid = ((first + third) >> 2) - (second >> 1) + origin[0x11];
    *high = first + third;
    b = *mid;
    a = *low;
    *firstOutput = a - origin[0x12];
    *secondOutput = b - origin[0x13];
}