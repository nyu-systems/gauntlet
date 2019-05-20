*** dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 16:58:29.632707500 +0200
--- dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 16:58:29.636221500 +0200
*************** control cIngress(inout headers hdr, inou
*** 353,367 ****
          hdr.h2 = hdr_1_h2;
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
!             hdr.h1.h2_valid_bits[0:0] = 1w1;
          if (hdr.h2[1].isValid()) 
!             hdr.h1.h2_valid_bits[1:1] = 1w1;
          if (hdr.h2[2].isValid()) 
!             hdr.h1.h2_valid_bits[2:2] = 1w1;
          if (hdr.h2[3].isValid()) 
!             hdr.h1.h2_valid_bits[3:3] = 1w1;
          if (hdr.h2[4].isValid()) 
!             hdr.h1.h2_valid_bits[4:4] = 1w1;
      }
  }
  control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
--- 353,367 ----
          hdr.h2 = hdr_1_h2;
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
!             hdr.h1.h2_valid_bits = hdr.h1.h2_valid_bits & ~8w0x1 | (bit<8>)1w1 << 0 & 8w0x1;
          if (hdr.h2[1].isValid()) 
!             hdr.h1.h2_valid_bits = hdr.h1.h2_valid_bits & ~8w0x2 | (bit<8>)1w1 << 1 & 8w0x2;
          if (hdr.h2[2].isValid()) 
!             hdr.h1.h2_valid_bits = hdr.h1.h2_valid_bits & ~8w0x4 | (bit<8>)1w1 << 2 & 8w0x4;
          if (hdr.h2[3].isValid()) 
!             hdr.h1.h2_valid_bits = hdr.h1.h2_valid_bits & ~8w0x8 | (bit<8>)1w1 << 3 & 8w0x8;
          if (hdr.h2[4].isValid()) 
!             hdr.h1.h2_valid_bits = hdr.h1.h2_valid_bits & ~8w0x10 | (bit<8>)1w1 << 4 & 8w0x10;
      }
  }
  control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
