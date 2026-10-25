#include "fixture.h"
extern u32 synthetic_select_0(u32, u32);
extern u32 synthetic_decode_0(u32, u32);
extern u32 synthetic_shape_0(u32, u32);
extern u32 synthetic_filter_0(u32, u32);
extern u32 synthetic_calibrate_0(u32, u32);
extern u32 synthetic_schedule_0(u32, u32);
extern u32 synthetic_select_1(u32, u32);
extern u32 synthetic_decode_1(u32, u32);
extern u32 synthetic_shape_1(u32, u32);
extern u32 synthetic_filter_1(u32, u32);
extern u32 synthetic_calibrate_1(u32, u32);
extern u32 synthetic_schedule_1(u32, u32);
extern u32 synthetic_select_2(u32, u32);
extern u32 synthetic_decode_2(u32, u32);
extern u32 synthetic_shape_2(u32, u32);
extern u32 synthetic_filter_2(u32, u32);
extern u32 synthetic_calibrate_2(u32, u32);
extern u32 synthetic_schedule_2(u32, u32);
extern u32 synthetic_select_3(u32, u32);
extern u32 synthetic_decode_3(u32, u32);
extern u32 synthetic_shape_3(u32, u32);
extern u32 synthetic_filter_3(u32, u32);
extern u32 synthetic_calibrate_3(u32, u32);
extern u32 synthetic_schedule_3(u32, u32);
extern u32 synthetic_select_4(u32, u32);
extern u32 synthetic_decode_4(u32, u32);
extern u32 synthetic_shape_4(u32, u32);
extern u32 synthetic_filter_4(u32, u32);
extern u32 synthetic_calibrate_4(u32, u32);
extern u32 synthetic_schedule_4(u32, u32);
extern u32 synthetic_select_5(u32, u32);
extern u32 synthetic_decode_5(u32, u32);
extern u32 synthetic_shape_5(u32, u32);
extern u32 synthetic_filter_5(u32, u32);
extern u32 synthetic_calibrate_5(u32, u32);
extern u32 synthetic_schedule_5(u32, u32);

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
        delay = synthetic_decode_0(delay, right);
        delay = synthetic_shape_0(delay, right);
        delay = synthetic_filter_0(delay, right);
        delay = synthetic_calibrate_0(delay, right);
        delay = synthetic_schedule_0(delay, right);
        break;
    case 1:
        delay = synthetic_select_1(left, right);
        delay = synthetic_decode_1(delay, right);
        delay = synthetic_shape_1(delay, right);
        delay = synthetic_filter_1(delay, right);
        delay = synthetic_calibrate_1(delay, right);
        delay = synthetic_schedule_1(delay, right);
        break;
    case 2:
        delay = synthetic_select_2(left, right);
        delay = synthetic_decode_2(delay, right);
        delay = synthetic_shape_2(delay, right);
        delay = synthetic_filter_2(delay, right);
        delay = synthetic_calibrate_2(delay, right);
        delay = synthetic_schedule_2(delay, right);
        break;
    case 3:
        delay = synthetic_select_3(left, right);
        delay = synthetic_decode_3(delay, right);
        delay = synthetic_shape_3(delay, right);
        delay = synthetic_filter_3(delay, right);
        delay = synthetic_calibrate_3(delay, right);
        delay = synthetic_schedule_3(delay, right);
        break;
    case 4:
        delay = synthetic_select_4(left, right);
        delay = synthetic_decode_4(delay, right);
        delay = synthetic_shape_4(delay, right);
        delay = synthetic_filter_4(delay, right);
        delay = synthetic_calibrate_4(delay, right);
        delay = synthetic_schedule_4(delay, right);
        break;
    case 5:
        delay = synthetic_select_5(left, right);
        delay = synthetic_decode_5(delay, right);
        delay = synthetic_shape_5(delay, right);
        delay = synthetic_filter_5(delay, right);
        delay = synthetic_calibrate_5(delay, right);
        delay = synthetic_schedule_5(delay, right);
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
