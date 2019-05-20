*** dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:29.621924600 +0200
--- dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:29.566715700 +0200
*************** control cIngress(inout headers hdr, inou
*** 63,71 ****
      headers hdr_1;
      bit<8> op;
      apply {
!         tmp_5 = hdr;
          tmp_6 = hdr.h1.op1;
!         hdr_1 = tmp_5;
          op = tmp_6;
          if (op == 8w0x0) 
              ;
--- 63,79 ----
      headers hdr_1;
      bit<8> op;
      apply {
!         {
!             tmp_5.h1 = hdr.h1;
!             tmp_5.h2 = hdr.h2;
!             tmp_5.h3 = hdr.h3;
!         }
          tmp_6 = hdr.h1.op1;
!         {
!             hdr_1.h1 = tmp_5.h1;
!             hdr_1.h2 = tmp_5.h2;
!             hdr_1.h3 = tmp_5.h3;
!         }
          op = tmp_6;
          if (op == 8w0x0) 
              ;
*************** control cIngress(inout headers hdr, inou
*** 164,174 ****
                                          else 
                                              if (op[3:0] == 4w4) 
                                                  hdr_1.h2[4].setInvalid();
!         tmp_5 = hdr_1;
!         hdr = tmp_5;
!         tmp_7 = hdr;
          tmp_8 = hdr.h1.op2;
!         hdr_1 = tmp_7;
          op = tmp_8;
          if (op == 8w0x0) 
              ;
--- 172,198 ----
                                          else 
                                              if (op[3:0] == 4w4) 
                                                  hdr_1.h2[4].setInvalid();
!         {
!             tmp_5.h1 = hdr_1.h1;
!             tmp_5.h2 = hdr_1.h2;
!             tmp_5.h3 = hdr_1.h3;
!         }
!         {
!             hdr.h1 = tmp_5.h1;
!             hdr.h2 = tmp_5.h2;
!             hdr.h3 = tmp_5.h3;
!         }
!         {
!             tmp_7.h1 = hdr.h1;
!             tmp_7.h2 = hdr.h2;
!             tmp_7.h3 = hdr.h3;
!         }
          tmp_8 = hdr.h1.op2;
!         {
!             hdr_1.h1 = tmp_7.h1;
!             hdr_1.h2 = tmp_7.h2;
!             hdr_1.h3 = tmp_7.h3;
!         }
          op = tmp_8;
          if (op == 8w0x0) 
              ;
*************** control cIngress(inout headers hdr, inou
*** 267,277 ****
                                          else 
                                              if (op[3:0] == 4w4) 
                                                  hdr_1.h2[4].setInvalid();
!         tmp_7 = hdr_1;
!         hdr = tmp_7;
!         tmp_9 = hdr;
          tmp_10 = hdr.h1.op3;
!         hdr_1 = tmp_9;
          op = tmp_10;
          if (op == 8w0x0) 
              ;
--- 291,317 ----
                                          else 
                                              if (op[3:0] == 4w4) 
                                                  hdr_1.h2[4].setInvalid();
!         {
!             tmp_7.h1 = hdr_1.h1;
!             tmp_7.h2 = hdr_1.h2;
!             tmp_7.h3 = hdr_1.h3;
!         }
!         {
!             hdr.h1 = tmp_7.h1;
!             hdr.h2 = tmp_7.h2;
!             hdr.h3 = tmp_7.h3;
!         }
!         {
!             tmp_9.h1 = hdr.h1;
!             tmp_9.h2 = hdr.h2;
!             tmp_9.h3 = hdr.h3;
!         }
          tmp_10 = hdr.h1.op3;
!         {
!             hdr_1.h1 = tmp_9.h1;
!             hdr_1.h2 = tmp_9.h2;
!             hdr_1.h3 = tmp_9.h3;
!         }
          op = tmp_10;
          if (op == 8w0x0) 
              ;
*************** control cIngress(inout headers hdr, inou
*** 370,377 ****
                                          else 
                                              if (op[3:0] == 4w4) 
                                                  hdr_1.h2[4].setInvalid();
!         tmp_9 = hdr_1;
!         hdr = tmp_9;
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
              hdr.h1.h2_valid_bits[0:0] = 1w1;
--- 410,425 ----
                                          else 
                                              if (op[3:0] == 4w4) 
                                                  hdr_1.h2[4].setInvalid();
!         {
!             tmp_9.h1 = hdr_1.h1;
!             tmp_9.h2 = hdr_1.h2;
!             tmp_9.h3 = hdr_1.h3;
!         }
!         {
!             hdr.h1 = tmp_9.h1;
!             hdr.h2 = tmp_9.h2;
!             hdr.h3 = tmp_9.h3;
!         }
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
              hdr.h1.h2_valid_bits[0:0] = 1w1;
