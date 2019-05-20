*** dumps/p4_16_samples/issue1127-bmv2.p4/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:39.485815100 +0200
--- dumps/p4_16_samples/issue1127-bmv2.p4/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:58:39.487657000 +0200
*************** parser parserI(packet_in pkt, out header
*** 17,66 ****
      }
  }
  control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
!     headers tmp_3;
      bit<8> tmp_4;
!     headers tmp_5;
      bit<8> tmp_6;
!     headers hdr_1;
      bit<8> op;
      apply {
          {
!             tmp_3.h1 = hdr.h1;
          }
          tmp_4 = hdr.h1.op1;
          {
!             hdr_1.h1 = tmp_3.h1;
          }
          op = tmp_4;
          if (op == 8w0x0) 
              ;
          else 
              if (op[7:4] == 4w1) 
!                 hdr_1.h1.out1 = 8w4;
          {
!             tmp_3.h1 = hdr_1.h1;
          }
          {
!             hdr.h1 = tmp_3.h1;
          }
          {
!             tmp_5.h1 = hdr.h1;
          }
          tmp_6 = hdr.h1.op2;
          {
!             hdr_1.h1 = tmp_5.h1;
          }
          op = tmp_6;
          if (op == 8w0x0) 
              ;
          else 
              if (op[7:4] == 4w1) 
!                 hdr_1.h1.out1 = 8w4;
          {
!             tmp_5.h1 = hdr_1.h1;
          }
          {
!             hdr.h1 = tmp_5.h1;
          }
      }
  }
--- 17,66 ----
      }
  }
  control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
!     h1_t tmp_3_h1;
      bit<8> tmp_4;
!     h1_t tmp_5_h1;
      bit<8> tmp_6;
!     h1_t hdr_1_h1;
      bit<8> op;
      apply {
          {
!             tmp_3_h1 = hdr.h1;
          }
          tmp_4 = hdr.h1.op1;
          {
!             hdr_1_h1 = tmp_3_h1;
          }
          op = tmp_4;
          if (op == 8w0x0) 
              ;
          else 
              if (op[7:4] == 4w1) 
!                 hdr_1_h1.out1 = 8w4;
          {
!             tmp_3_h1 = hdr_1_h1;
          }
          {
!             hdr.h1 = tmp_3_h1;
          }
          {
!             tmp_5_h1 = hdr.h1;
          }
          tmp_6 = hdr.h1.op2;
          {
!             hdr_1_h1 = tmp_5_h1;
          }
          op = tmp_6;
          if (op == 8w0x0) 
              ;
          else 
              if (op[7:4] == 4w1) 
!                 hdr_1_h1.out1 = 8w4;
          {
!             tmp_5_h1 = hdr_1_h1;
          }
          {
!             hdr.h1 = tmp_5_h1;
          }
      }
  }
