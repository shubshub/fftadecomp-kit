typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;

struct Parameters {
    u16 delay;
    u8 count;
    u8 reserved;
    void *data;
};

struct Descriptor {
    u16 phase;
    u16 reserved;
    struct Parameters *parameters;
    u32 words[5];
};

typedef u32 (*Callback)(void *, struct Descriptor *, void *);
typedef char descriptor_must_be_28[sizeof(struct Descriptor) == 28 ? 1 : -1];
typedef char parameters_must_be_8[sizeof(struct Parameters) == 8 ? 1 : -1];

extern void *manager_cell;
extern u32 synthetic_callback(void *, struct Descriptor *, void *);
extern void *synthetic_registration(void *, Callback, u32,
                                    struct Descriptor *, void *);
