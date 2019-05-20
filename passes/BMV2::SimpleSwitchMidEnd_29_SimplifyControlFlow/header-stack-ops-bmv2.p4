*** dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:29.746147400 +0200
--- dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:29.749919200 +0200
*************** parser parserI(packet_in pkt, out header
*** 56,66 ****
  control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
      h2_t[5] hdr_1_h2;
      apply {
!         {
!         }
!         {
!             hdr_1_h2 = hdr.h2;
!         }
          if (hdr.h1.op1 == 8w0x0) 
              ;
          else 
--- 56,62 ----
  control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
      h2_t[5] hdr_1_h2;
      apply {
!         hdr_1_h2 = hdr.h2;
          if (hdr.h1.op1 == 8w0x0) 
              ;
          else 
*************** control cIngress(inout headers hdr, inou
*** 158,172 ****
                                          else 
                                              if (hdr.h1.op1[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
!         {
!         }
!         {
!             hdr.h2 = hdr_1_h2;
!         }
!         {
!         }
!         {
!         }
          if (hdr.h1.op2 == 8w0x0) 
              ;
          else 
--- 154,160 ----
                                          else 
                                              if (hdr.h1.op1[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
!         hdr.h2 = hdr_1_h2;
          if (hdr.h1.op2 == 8w0x0) 
              ;
          else 
*************** control cIngress(inout headers hdr, inou
*** 264,278 ****
                                          else 
                                              if (hdr.h1.op2[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
!         {
!         }
!         {
!             hdr.h2 = hdr_1_h2;
!         }
!         {
!         }
!         {
!         }
          if (hdr.h1.op3 == 8w0x0) 
              ;
          else 
--- 252,258 ----
                                          else 
                                              if (hdr.h1.op2[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
!         hdr.h2 = hdr_1_h2;
          if (hdr.h1.op3 == 8w0x0) 
              ;
          else 
*************** control cIngress(inout headers hdr, inou
*** 370,380 ****
                                          else 
                                              if (hdr.h1.op3[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
!         {
!         }
!         {
!             hdr.h2 = hdr_1_h2;
!         }
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
              hdr.h1.h2_valid_bits[0:0] = 1w1;
--- 350,356 ----
                                          else 
                                              if (hdr.h1.op3[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
!         hdr.h2 = hdr_1_h2;
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
              hdr.h1.h2_valid_bits[0:0] = 1w1;
*************** control uc(inout headers hdr, inout meta
*** 403,415 ****
  control DeparserI(packet_out packet, in headers hdr) {
      apply {
          packet.emit<h1_t>(hdr.h1);
!         {
!             packet.emit<h2_t>(hdr.h2[0]);
!             packet.emit<h2_t>(hdr.h2[1]);
!             packet.emit<h2_t>(hdr.h2[2]);
!             packet.emit<h2_t>(hdr.h2[3]);
!             packet.emit<h2_t>(hdr.h2[4]);
!         }
          packet.emit<h3_t>(hdr.h3);
      }
  }
--- 379,389 ----
  control DeparserI(packet_out packet, in headers hdr) {
      apply {
          packet.emit<h1_t>(hdr.h1);
!         packet.emit<h2_t>(hdr.h2[0]);
!         packet.emit<h2_t>(hdr.h2[1]);
!         packet.emit<h2_t>(hdr.h2[2]);
!         packet.emit<h2_t>(hdr.h2[3]);
!         packet.emit<h2_t>(hdr.h2[4]);
          packet.emit<h3_t>(hdr.h3);
      }
  }
