#include "fixture.h"
extern u32 synthetic_select_0(u32, u32);
extern u32 synthetic_select_1(u32, u32);
extern u32 synthetic_select_2(u32, u32);
extern u32 synthetic_select_3(u32, u32);
extern u32 synthetic_select_4(u32, u32);
extern u32 synthetic_select_5(u32, u32);

void *func_08000000(u32 selector, u32 count, void *data, void *parent,
                       u32 left, u32 right)
{
    struct Descriptor descriptor;
    struct Parameters parameters;
    u32 delay;

    selector &= 255;
    count &= 255;
    if (count == 0 || selector == 7)
        return 0;
    left &= 0xFF00FF00;
    right &= 0x0F0F0F0F;
    switch (selector) {
    case 0:
        delay = synthetic_select_0(left, right);

        break;
    case 1:
        delay = synthetic_select_1(left, right);

        break;
    case 2:
        delay = synthetic_select_2(left, right);

        break;
    case 3:
        delay = synthetic_select_3(left, right);

        break;
    case 4:
        delay = synthetic_select_4(left, right);

        break;
    case 5:
        delay = synthetic_select_5(left, right);

        break;
    default:
        return 0;
    }
    parameters.delay = delay;
    parameters.count = count;
    parameters.data = data;
    descriptor.phase = 0;
    descriptor.parameters = &parameters;
    return synthetic_registration(manager_cell, synthetic_callback, 12,
                                  &descriptor, parent);
}
