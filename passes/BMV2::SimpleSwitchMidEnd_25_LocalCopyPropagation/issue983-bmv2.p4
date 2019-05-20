*** dumps/p4_16_samples/issue983-bmv2.p4/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:40.267850100 +0200
--- dumps/p4_16_samples/issue983-bmv2.p4/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:40.271206100 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 31,39 ****
      }
  }
  control ingress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
-     bit<16> tmp_1;
-     bit<32> x1_1;
-     bit<16> x2_1;
      @name(".NoAction") action NoAction_0() {
      }
      @name("ingress.debug_table_cksum1") table debug_table_cksum1 {
--- 31,36 ----
*************** control ingress(inout headers hdr, inout
*** 58,69 ****
          default_action = NoAction_0();
      }
      apply {
!         tmp_1 = ~hdr.ethernet.etherType;
!         x1_1 = (bit<32>)tmp_1;
!         x2_1 = x1_1[31:16] + x1_1[15:0];
!         user_meta.fwd_meta.tmp = tmp_1;
!         user_meta.fwd_meta.x1 = x1_1;
!         user_meta.fwd_meta.x2 = x2_1;
          user_meta.fwd_meta.x3 = (bit<32>)~hdr.ethernet.etherType;
          user_meta.fwd_meta.x4 = ~(bit<32>)hdr.ethernet.etherType;
          user_meta.fwd_meta.exp_etherType = 16w0x800;
--- 55,63 ----
          default_action = NoAction_0();
      }
      apply {
!         user_meta.fwd_meta.tmp = ~hdr.ethernet.etherType;
!         user_meta.fwd_meta.x1 = (bit<32>)~hdr.ethernet.etherType;
!         user_meta.fwd_meta.x2 = ((bit<32>)~hdr.ethernet.etherType)[31:16] + ((bit<32>)~hdr.ethernet.etherType)[15:0];
          user_meta.fwd_meta.x3 = (bit<32>)~hdr.ethernet.etherType;
          user_meta.fwd_meta.x4 = ~(bit<32>)hdr.ethernet.etherType;
          user_meta.fwd_meta.exp_etherType = 16w0x800;
*************** control ingress(inout headers hdr, inout
*** 72,86 ****
          user_meta.fwd_meta.exp_x3 = 32w0xf7ff;
          user_meta.fwd_meta.exp_x4 = 32w0xfffff7ff;
          hdr.ethernet.dstAddr = 48w0;
!         if (hdr.ethernet.etherType != user_meta.fwd_meta.exp_etherType) 
              hdr.ethernet.dstAddr[47:40] = 8w1;
!         if (user_meta.fwd_meta.x1 != user_meta.fwd_meta.exp_x1) 
              hdr.ethernet.dstAddr[39:32] = 8w1;
!         if (user_meta.fwd_meta.x2 != user_meta.fwd_meta.exp_x2) 
              hdr.ethernet.dstAddr[31:24] = 8w1;
!         if (user_meta.fwd_meta.x3 != user_meta.fwd_meta.exp_x3) 
              hdr.ethernet.dstAddr[23:16] = 8w1;
!         if (user_meta.fwd_meta.x4 != user_meta.fwd_meta.exp_x4) 
              hdr.ethernet.dstAddr[15:8] = 8w1;
          debug_table_cksum1.apply();
      }
--- 66,80 ----
          user_meta.fwd_meta.exp_x3 = 32w0xf7ff;
          user_meta.fwd_meta.exp_x4 = 32w0xfffff7ff;
          hdr.ethernet.dstAddr = 48w0;
!         if (hdr.ethernet.etherType != 16w0x800) 
              hdr.ethernet.dstAddr[47:40] = 8w1;
!         if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
              hdr.ethernet.dstAddr[39:32] = 8w1;
!         if (((bit<32>)~hdr.ethernet.etherType)[31:16] + ((bit<32>)~hdr.ethernet.etherType)[15:0] != 16w0xf7ff) 
              hdr.ethernet.dstAddr[31:24] = 8w1;
!         if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
              hdr.ethernet.dstAddr[23:16] = 8w1;
!         if (~(bit<32>)hdr.ethernet.etherType != 32w0xfffff7ff) 
              hdr.ethernet.dstAddr[15:8] = 8w1;
          debug_table_cksum1.apply();
      }
