*** dumps/p4_16_samples/issue983-bmv2.p4/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 16:59:40.292708500 +0200
--- dumps/p4_16_samples/issue983-bmv2.p4/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 16:59:40.296228600 +0200
*************** control ingress(inout headers hdr, inout
*** 67,81 ****
          user_meta.fwd_meta.exp_x4 = 32w0xfffff7ff;
          hdr.ethernet.dstAddr = 48w0;
          if (hdr.ethernet.etherType != 16w0x800) 
!             hdr.ethernet.dstAddr[47:40] = 8w1;
          if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
!             hdr.ethernet.dstAddr[39:32] = 8w1;
          if (((bit<32>)~hdr.ethernet.etherType)[31:16] + ((bit<32>)~hdr.ethernet.etherType)[15:0] != 16w0xf7ff) 
!             hdr.ethernet.dstAddr[31:24] = 8w1;
          if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
!             hdr.ethernet.dstAddr[23:16] = 8w1;
          if (~(bit<32>)hdr.ethernet.etherType != 32w0xfffff7ff) 
!             hdr.ethernet.dstAddr[15:8] = 8w1;
          debug_table_cksum1.apply();
      }
  }
--- 67,81 ----
          user_meta.fwd_meta.exp_x4 = 32w0xfffff7ff;
          hdr.ethernet.dstAddr = 48w0;
          if (hdr.ethernet.etherType != 16w0x800) 
!             hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff0000000000 | (bit<48>)8w1 << 40 & 48w0xff0000000000;
          if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
!             hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff00000000 | (bit<48>)8w1 << 32 & 48w0xff00000000;
          if (((bit<32>)~hdr.ethernet.etherType)[31:16] + ((bit<32>)~hdr.ethernet.etherType)[15:0] != 16w0xf7ff) 
!             hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff000000 | (bit<48>)8w1 << 24 & 48w0xff000000;
          if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
!             hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff0000 | (bit<48>)8w1 << 16 & 48w0xff0000;
          if (~(bit<32>)hdr.ethernet.etherType != 32w0xfffff7ff) 
!             hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff00 | (bit<48>)8w1 << 8 & 48w0xff00;
          debug_table_cksum1.apply();
      }
  }
