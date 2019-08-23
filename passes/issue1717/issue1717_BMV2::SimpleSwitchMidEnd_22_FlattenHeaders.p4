header H {
    bit<32> isValid;
}
typedef bit<32> T;
header H1 {
    bit<16> f;
    bit<8>  minSizeInBytes;
    bit<8>  minSizeInBits;
    T       f1;
    bit<16> e;
}
struct Flags {
    bit<1> f0;
    bit<1> f1;
    bit<6> pad;
}
header Nested {
    bit<1>     _flags_f00;
    bit<1>     _flags_f11;
    bit<6>     _flags_pad2;
    bit<32>    _b3;
    varbit<32> _v4;
}
struct S {
    H    h1;
    H1   h2;
    H[3] h3;
}
header_union HU {
    H  h1;
    H1 h2;
}
header Empty {
}
