*** dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:29.728061000 +0200
--- dumps/p4_16_samples/header-stack-ops-bmv2.p4/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:29.732033000 +0200
*************** parser parserI(packet_in pkt, out header
*** 54,131 ****
      }
  }
  control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
-     h1_t tmp_5_h1;
-     h2_t[5] tmp_5_h2;
-     h3_t tmp_5_h3;
-     bit<8> tmp_6;
-     h1_t tmp_7_h1;
-     h2_t[5] tmp_7_h2;
-     h3_t tmp_7_h3;
-     bit<8> tmp_8;
-     h1_t tmp_9_h1;
-     h2_t[5] tmp_9_h2;
-     h3_t tmp_9_h3;
-     bit<8> tmp_10;
-     h1_t hdr_1_h1;
      h2_t[5] hdr_1_h2;
-     h3_t hdr_1_h3;
-     bit<8> op;
      apply {
          {
-             tmp_5_h1 = hdr.h1;
-             tmp_5_h2 = hdr.h2;
-             tmp_5_h3 = hdr.h3;
-         }
-         tmp_6 = hdr.h1.op1;
-         {
-             hdr_1_h1 = tmp_5_h1;
-             hdr_1_h2 = tmp_5_h2;
-             hdr_1_h3 = tmp_5_h3;
          }
!         op = tmp_6;
!         if (op == 8w0x0) 
              ;
          else 
!             if (op[7:4] == 4w1) 
!                 if (op[3:0] == 4w1) 
                      hdr_1_h2.push_front(1);
                  else 
!                     if (op[3:0] == 4w2) 
                          hdr_1_h2.push_front(2);
                      else 
!                         if (op[3:0] == 4w3) 
                              hdr_1_h2.push_front(3);
                          else 
!                             if (op[3:0] == 4w4) 
                                  hdr_1_h2.push_front(4);
                              else 
!                                 if (op[3:0] == 4w5) 
                                      hdr_1_h2.push_front(5);
                                  else 
!                                     if (op[3:0] == 4w6) 
                                          hdr_1_h2.push_front(6);
              else 
!                 if (op[7:4] == 4w2) 
!                     if (op[3:0] == 4w1) 
                          hdr_1_h2.pop_front(1);
                      else 
!                         if (op[3:0] == 4w2) 
                              hdr_1_h2.pop_front(2);
                          else 
!                             if (op[3:0] == 4w3) 
                                  hdr_1_h2.pop_front(3);
                              else 
!                                 if (op[3:0] == 4w4) 
                                      hdr_1_h2.pop_front(4);
                                  else 
!                                     if (op[3:0] == 4w5) 
                                          hdr_1_h2.pop_front(5);
                                      else 
!                                         if (op[3:0] == 4w6) 
                                              hdr_1_h2.pop_front(6);
                  else 
!                     if (op[7:4] == 4w3) 
!                         if (op[3:0] == 4w0) {
                              hdr_1_h2[0].setValid();
                              hdr_1_h2[0].hdr_type = 8w2;
                              hdr_1_h2[0].f1 = 8w0xa0;
--- 54,109 ----
      }
  }
  control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
      h2_t[5] hdr_1_h2;
      apply {
          {
          }
!         {
!             hdr_1_h2 = hdr.h2;
!         }
!         if (hdr.h1.op1 == 8w0x0) 
              ;
          else 
!             if (hdr.h1.op1[7:4] == 4w1) 
!                 if (hdr.h1.op1[3:0] == 4w1) 
                      hdr_1_h2.push_front(1);
                  else 
!                     if (hdr.h1.op1[3:0] == 4w2) 
                          hdr_1_h2.push_front(2);
                      else 
!                         if (hdr.h1.op1[3:0] == 4w3) 
                              hdr_1_h2.push_front(3);
                          else 
!                             if (hdr.h1.op1[3:0] == 4w4) 
                                  hdr_1_h2.push_front(4);
                              else 
!                                 if (hdr.h1.op1[3:0] == 4w5) 
                                      hdr_1_h2.push_front(5);
                                  else 
!                                     if (hdr.h1.op1[3:0] == 4w6) 
                                          hdr_1_h2.push_front(6);
              else 
!                 if (hdr.h1.op1[7:4] == 4w2) 
!                     if (hdr.h1.op1[3:0] == 4w1) 
                          hdr_1_h2.pop_front(1);
                      else 
!                         if (hdr.h1.op1[3:0] == 4w2) 
                              hdr_1_h2.pop_front(2);
                          else 
!                             if (hdr.h1.op1[3:0] == 4w3) 
                                  hdr_1_h2.pop_front(3);
                              else 
!                                 if (hdr.h1.op1[3:0] == 4w4) 
                                      hdr_1_h2.pop_front(4);
                                  else 
!                                     if (hdr.h1.op1[3:0] == 4w5) 
                                          hdr_1_h2.pop_front(5);
                                      else 
!                                         if (hdr.h1.op1[3:0] == 4w6) 
                                              hdr_1_h2.pop_front(6);
                  else 
!                     if (hdr.h1.op1[7:4] == 4w3) 
!                         if (hdr.h1.op1[3:0] == 4w0) {
                              hdr_1_h2[0].setValid();
                              hdr_1_h2[0].hdr_type = 8w2;
                              hdr_1_h2[0].f1 = 8w0xa0;
*************** control cIngress(inout headers hdr, inou
*** 133,139 ****
                              hdr_1_h2[0].next_hdr_type = 8w9;
                          }
                          else 
!                             if (op[3:0] == 4w1) {
                                  hdr_1_h2[1].setValid();
                                  hdr_1_h2[1].hdr_type = 8w2;
                                  hdr_1_h2[1].f1 = 8w0xa1;
--- 111,117 ----
                              hdr_1_h2[0].next_hdr_type = 8w9;
                          }
                          else 
!                             if (hdr.h1.op1[3:0] == 4w1) {
                                  hdr_1_h2[1].setValid();
                                  hdr_1_h2[1].hdr_type = 8w2;
                                  hdr_1_h2[1].f1 = 8w0xa1;
*************** control cIngress(inout headers hdr, inou
*** 141,147 ****
                                  hdr_1_h2[1].next_hdr_type = 8w9;
                              }
                              else 
!                                 if (op[3:0] == 4w2) {
                                      hdr_1_h2[2].setValid();
                                      hdr_1_h2[2].hdr_type = 8w2;
                                      hdr_1_h2[2].f1 = 8w0xa2;
--- 119,125 ----
                                  hdr_1_h2[1].next_hdr_type = 8w9;
                              }
                              else 
!                                 if (hdr.h1.op1[3:0] == 4w2) {
                                      hdr_1_h2[2].setValid();
                                      hdr_1_h2[2].hdr_type = 8w2;
                                      hdr_1_h2[2].f1 = 8w0xa2;
*************** control cIngress(inout headers hdr, inou
*** 149,155 ****
                                      hdr_1_h2[2].next_hdr_type = 8w9;
                                  }
                                  else 
!                                     if (op[3:0] == 4w3) {
                                          hdr_1_h2[3].setValid();
                                          hdr_1_h2[3].hdr_type = 8w2;
                                          hdr_1_h2[3].f1 = 8w0xa3;
--- 127,133 ----
                                      hdr_1_h2[2].next_hdr_type = 8w9;
                                  }
                                  else 
!                                     if (hdr.h1.op1[3:0] == 4w3) {
                                          hdr_1_h2[3].setValid();
                                          hdr_1_h2[3].hdr_type = 8w2;
                                          hdr_1_h2[3].f1 = 8w0xa3;
*************** control cIngress(inout headers hdr, inou
*** 157,163 ****
                                          hdr_1_h2[3].next_hdr_type = 8w9;
                                      }
                                      else 
!                                         if (op[3:0] == 4w4) {
                                              hdr_1_h2[4].setValid();
                                              hdr_1_h2[4].hdr_type = 8w2;
                                              hdr_1_h2[4].f1 = 8w0xa4;
--- 135,141 ----
                                          hdr_1_h2[3].next_hdr_type = 8w9;
                                      }
                                      else 
!                                         if (hdr.h1.op1[3:0] == 4w4) {
                                              hdr_1_h2[4].setValid();
                                              hdr_1_h2[4].hdr_type = 8w2;
                                              hdr_1_h2[4].f1 = 8w0xa4;
*************** control cIngress(inout headers hdr, inou
*** 165,250 ****
                                              hdr_1_h2[4].next_hdr_type = 8w9;
                                          }
                      else 
!                         if (op[7:4] == 4w4) 
!                             if (op[3:0] == 4w0) 
                                  hdr_1_h2[0].setInvalid();
                              else 
!                                 if (op[3:0] == 4w1) 
                                      hdr_1_h2[1].setInvalid();
                                  else 
!                                     if (op[3:0] == 4w2) 
                                          hdr_1_h2[2].setInvalid();
                                      else 
!                                         if (op[3:0] == 4w3) 
                                              hdr_1_h2[3].setInvalid();
                                          else 
!                                             if (op[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
          {
-             tmp_5_h1 = hdr_1_h1;
-             tmp_5_h2 = hdr_1_h2;
-             tmp_5_h3 = hdr_1_h3;
          }
          {
!             hdr.h1 = tmp_5_h1;
!             hdr.h2 = tmp_5_h2;
!             hdr.h3 = tmp_5_h3;
          }
          {
-             tmp_7_h1 = hdr.h1;
-             tmp_7_h2 = hdr.h2;
-             tmp_7_h3 = hdr.h3;
          }
-         tmp_8 = hdr.h1.op2;
          {
-             hdr_1_h1 = tmp_7_h1;
-             hdr_1_h2 = tmp_7_h2;
-             hdr_1_h3 = tmp_7_h3;
          }
!         op = tmp_8;
!         if (op == 8w0x0) 
              ;
          else 
!             if (op[7:4] == 4w1) 
!                 if (op[3:0] == 4w1) 
                      hdr_1_h2.push_front(1);
                  else 
!                     if (op[3:0] == 4w2) 
                          hdr_1_h2.push_front(2);
                      else 
!                         if (op[3:0] == 4w3) 
                              hdr_1_h2.push_front(3);
                          else 
!                             if (op[3:0] == 4w4) 
                                  hdr_1_h2.push_front(4);
                              else 
!                                 if (op[3:0] == 4w5) 
                                      hdr_1_h2.push_front(5);
                                  else 
!                                     if (op[3:0] == 4w6) 
                                          hdr_1_h2.push_front(6);
              else 
!                 if (op[7:4] == 4w2) 
!                     if (op[3:0] == 4w1) 
                          hdr_1_h2.pop_front(1);
                      else 
!                         if (op[3:0] == 4w2) 
                              hdr_1_h2.pop_front(2);
                          else 
!                             if (op[3:0] == 4w3) 
                                  hdr_1_h2.pop_front(3);
                              else 
!                                 if (op[3:0] == 4w4) 
                                      hdr_1_h2.pop_front(4);
                                  else 
!                                     if (op[3:0] == 4w5) 
                                          hdr_1_h2.pop_front(5);
                                      else 
!                                         if (op[3:0] == 4w6) 
                                              hdr_1_h2.pop_front(6);
                  else 
!                     if (op[7:4] == 4w3) 
!                         if (op[3:0] == 4w0) {
                              hdr_1_h2[0].setValid();
                              hdr_1_h2[0].hdr_type = 8w2;
                              hdr_1_h2[0].f1 = 8w0xa0;
--- 143,215 ----
                                              hdr_1_h2[4].next_hdr_type = 8w9;
                                          }
                      else 
!                         if (hdr.h1.op1[7:4] == 4w4) 
!                             if (hdr.h1.op1[3:0] == 4w0) 
                                  hdr_1_h2[0].setInvalid();
                              else 
!                                 if (hdr.h1.op1[3:0] == 4w1) 
                                      hdr_1_h2[1].setInvalid();
                                  else 
!                                     if (hdr.h1.op1[3:0] == 4w2) 
                                          hdr_1_h2[2].setInvalid();
                                      else 
!                                         if (hdr.h1.op1[3:0] == 4w3) 
                                              hdr_1_h2[3].setInvalid();
                                          else 
!                                             if (hdr.h1.op1[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
          {
          }
          {
!             hdr.h2 = hdr_1_h2;
          }
          {
          }
          {
          }
!         if (hdr.h1.op2 == 8w0x0) 
              ;
          else 
!             if (hdr.h1.op2[7:4] == 4w1) 
!                 if (hdr.h1.op2[3:0] == 4w1) 
                      hdr_1_h2.push_front(1);
                  else 
!                     if (hdr.h1.op2[3:0] == 4w2) 
                          hdr_1_h2.push_front(2);
                      else 
!                         if (hdr.h1.op2[3:0] == 4w3) 
                              hdr_1_h2.push_front(3);
                          else 
!                             if (hdr.h1.op2[3:0] == 4w4) 
                                  hdr_1_h2.push_front(4);
                              else 
!                                 if (hdr.h1.op2[3:0] == 4w5) 
                                      hdr_1_h2.push_front(5);
                                  else 
!                                     if (hdr.h1.op2[3:0] == 4w6) 
                                          hdr_1_h2.push_front(6);
              else 
!                 if (hdr.h1.op2[7:4] == 4w2) 
!                     if (hdr.h1.op2[3:0] == 4w1) 
                          hdr_1_h2.pop_front(1);
                      else 
!                         if (hdr.h1.op2[3:0] == 4w2) 
                              hdr_1_h2.pop_front(2);
                          else 
!                             if (hdr.h1.op2[3:0] == 4w3) 
                                  hdr_1_h2.pop_front(3);
                              else 
!                                 if (hdr.h1.op2[3:0] == 4w4) 
                                      hdr_1_h2.pop_front(4);
                                  else 
!                                     if (hdr.h1.op2[3:0] == 4w5) 
                                          hdr_1_h2.pop_front(5);
                                      else 
!                                         if (hdr.h1.op2[3:0] == 4w6) 
                                              hdr_1_h2.pop_front(6);
                  else 
!                     if (hdr.h1.op2[7:4] == 4w3) 
!                         if (hdr.h1.op2[3:0] == 4w0) {
                              hdr_1_h2[0].setValid();
                              hdr_1_h2[0].hdr_type = 8w2;
                              hdr_1_h2[0].f1 = 8w0xa0;
*************** control cIngress(inout headers hdr, inou
*** 252,258 ****
                              hdr_1_h2[0].next_hdr_type = 8w9;
                          }
                          else 
!                             if (op[3:0] == 4w1) {
                                  hdr_1_h2[1].setValid();
                                  hdr_1_h2[1].hdr_type = 8w2;
                                  hdr_1_h2[1].f1 = 8w0xa1;
--- 217,223 ----
                              hdr_1_h2[0].next_hdr_type = 8w9;
                          }
                          else 
!                             if (hdr.h1.op2[3:0] == 4w1) {
                                  hdr_1_h2[1].setValid();
                                  hdr_1_h2[1].hdr_type = 8w2;
                                  hdr_1_h2[1].f1 = 8w0xa1;
*************** control cIngress(inout headers hdr, inou
*** 260,266 ****
                                  hdr_1_h2[1].next_hdr_type = 8w9;
                              }
                              else 
!                                 if (op[3:0] == 4w2) {
                                      hdr_1_h2[2].setValid();
                                      hdr_1_h2[2].hdr_type = 8w2;
                                      hdr_1_h2[2].f1 = 8w0xa2;
--- 225,231 ----
                                  hdr_1_h2[1].next_hdr_type = 8w9;
                              }
                              else 
!                                 if (hdr.h1.op2[3:0] == 4w2) {
                                      hdr_1_h2[2].setValid();
                                      hdr_1_h2[2].hdr_type = 8w2;
                                      hdr_1_h2[2].f1 = 8w0xa2;
*************** control cIngress(inout headers hdr, inou
*** 268,274 ****
                                      hdr_1_h2[2].next_hdr_type = 8w9;
                                  }
                                  else 
!                                     if (op[3:0] == 4w3) {
                                          hdr_1_h2[3].setValid();
                                          hdr_1_h2[3].hdr_type = 8w2;
                                          hdr_1_h2[3].f1 = 8w0xa3;
--- 233,239 ----
                                      hdr_1_h2[2].next_hdr_type = 8w9;
                                  }
                                  else 
!                                     if (hdr.h1.op2[3:0] == 4w3) {
                                          hdr_1_h2[3].setValid();
                                          hdr_1_h2[3].hdr_type = 8w2;
                                          hdr_1_h2[3].f1 = 8w0xa3;
*************** control cIngress(inout headers hdr, inou
*** 276,282 ****
                                          hdr_1_h2[3].next_hdr_type = 8w9;
                                      }
                                      else 
!                                         if (op[3:0] == 4w4) {
                                              hdr_1_h2[4].setValid();
                                              hdr_1_h2[4].hdr_type = 8w2;
                                              hdr_1_h2[4].f1 = 8w0xa4;
--- 241,247 ----
                                          hdr_1_h2[3].next_hdr_type = 8w9;
                                      }
                                      else 
!                                         if (hdr.h1.op2[3:0] == 4w4) {
                                              hdr_1_h2[4].setValid();
                                              hdr_1_h2[4].hdr_type = 8w2;
                                              hdr_1_h2[4].f1 = 8w0xa4;
*************** control cIngress(inout headers hdr, inou
*** 284,369 ****
                                              hdr_1_h2[4].next_hdr_type = 8w9;
                                          }
                      else 
!                         if (op[7:4] == 4w4) 
!                             if (op[3:0] == 4w0) 
                                  hdr_1_h2[0].setInvalid();
                              else 
!                                 if (op[3:0] == 4w1) 
                                      hdr_1_h2[1].setInvalid();
                                  else 
!                                     if (op[3:0] == 4w2) 
                                          hdr_1_h2[2].setInvalid();
                                      else 
!                                         if (op[3:0] == 4w3) 
                                              hdr_1_h2[3].setInvalid();
                                          else 
!                                             if (op[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
          {
-             tmp_7_h1 = hdr_1_h1;
-             tmp_7_h2 = hdr_1_h2;
-             tmp_7_h3 = hdr_1_h3;
          }
          {
!             hdr.h1 = tmp_7_h1;
!             hdr.h2 = tmp_7_h2;
!             hdr.h3 = tmp_7_h3;
          }
          {
-             tmp_9_h1 = hdr.h1;
-             tmp_9_h2 = hdr.h2;
-             tmp_9_h3 = hdr.h3;
          }
-         tmp_10 = hdr.h1.op3;
          {
-             hdr_1_h1 = tmp_9_h1;
-             hdr_1_h2 = tmp_9_h2;
-             hdr_1_h3 = tmp_9_h3;
          }
!         op = tmp_10;
!         if (op == 8w0x0) 
              ;
          else 
!             if (op[7:4] == 4w1) 
!                 if (op[3:0] == 4w1) 
                      hdr_1_h2.push_front(1);
                  else 
!                     if (op[3:0] == 4w2) 
                          hdr_1_h2.push_front(2);
                      else 
!                         if (op[3:0] == 4w3) 
                              hdr_1_h2.push_front(3);
                          else 
!                             if (op[3:0] == 4w4) 
                                  hdr_1_h2.push_front(4);
                              else 
!                                 if (op[3:0] == 4w5) 
                                      hdr_1_h2.push_front(5);
                                  else 
!                                     if (op[3:0] == 4w6) 
                                          hdr_1_h2.push_front(6);
              else 
!                 if (op[7:4] == 4w2) 
!                     if (op[3:0] == 4w1) 
                          hdr_1_h2.pop_front(1);
                      else 
!                         if (op[3:0] == 4w2) 
                              hdr_1_h2.pop_front(2);
                          else 
!                             if (op[3:0] == 4w3) 
                                  hdr_1_h2.pop_front(3);
                              else 
!                                 if (op[3:0] == 4w4) 
                                      hdr_1_h2.pop_front(4);
                                  else 
!                                     if (op[3:0] == 4w5) 
                                          hdr_1_h2.pop_front(5);
                                      else 
!                                         if (op[3:0] == 4w6) 
                                              hdr_1_h2.pop_front(6);
                  else 
!                     if (op[7:4] == 4w3) 
!                         if (op[3:0] == 4w0) {
                              hdr_1_h2[0].setValid();
                              hdr_1_h2[0].hdr_type = 8w2;
                              hdr_1_h2[0].f1 = 8w0xa0;
--- 249,321 ----
                                              hdr_1_h2[4].next_hdr_type = 8w9;
                                          }
                      else 
!                         if (hdr.h1.op2[7:4] == 4w4) 
!                             if (hdr.h1.op2[3:0] == 4w0) 
                                  hdr_1_h2[0].setInvalid();
                              else 
!                                 if (hdr.h1.op2[3:0] == 4w1) 
                                      hdr_1_h2[1].setInvalid();
                                  else 
!                                     if (hdr.h1.op2[3:0] == 4w2) 
                                          hdr_1_h2[2].setInvalid();
                                      else 
!                                         if (hdr.h1.op2[3:0] == 4w3) 
                                              hdr_1_h2[3].setInvalid();
                                          else 
!                                             if (hdr.h1.op2[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
          {
          }
          {
!             hdr.h2 = hdr_1_h2;
          }
          {
          }
          {
          }
!         if (hdr.h1.op3 == 8w0x0) 
              ;
          else 
!             if (hdr.h1.op3[7:4] == 4w1) 
!                 if (hdr.h1.op3[3:0] == 4w1) 
                      hdr_1_h2.push_front(1);
                  else 
!                     if (hdr.h1.op3[3:0] == 4w2) 
                          hdr_1_h2.push_front(2);
                      else 
!                         if (hdr.h1.op3[3:0] == 4w3) 
                              hdr_1_h2.push_front(3);
                          else 
!                             if (hdr.h1.op3[3:0] == 4w4) 
                                  hdr_1_h2.push_front(4);
                              else 
!                                 if (hdr.h1.op3[3:0] == 4w5) 
                                      hdr_1_h2.push_front(5);
                                  else 
!                                     if (hdr.h1.op3[3:0] == 4w6) 
                                          hdr_1_h2.push_front(6);
              else 
!                 if (hdr.h1.op3[7:4] == 4w2) 
!                     if (hdr.h1.op3[3:0] == 4w1) 
                          hdr_1_h2.pop_front(1);
                      else 
!                         if (hdr.h1.op3[3:0] == 4w2) 
                              hdr_1_h2.pop_front(2);
                          else 
!                             if (hdr.h1.op3[3:0] == 4w3) 
                                  hdr_1_h2.pop_front(3);
                              else 
!                                 if (hdr.h1.op3[3:0] == 4w4) 
                                      hdr_1_h2.pop_front(4);
                                  else 
!                                     if (hdr.h1.op3[3:0] == 4w5) 
                                          hdr_1_h2.pop_front(5);
                                      else 
!                                         if (hdr.h1.op3[3:0] == 4w6) 
                                              hdr_1_h2.pop_front(6);
                  else 
!                     if (hdr.h1.op3[7:4] == 4w3) 
!                         if (hdr.h1.op3[3:0] == 4w0) {
                              hdr_1_h2[0].setValid();
                              hdr_1_h2[0].hdr_type = 8w2;
                              hdr_1_h2[0].f1 = 8w0xa0;
*************** control cIngress(inout headers hdr, inou
*** 371,377 ****
                              hdr_1_h2[0].next_hdr_type = 8w9;
                          }
                          else 
!                             if (op[3:0] == 4w1) {
                                  hdr_1_h2[1].setValid();
                                  hdr_1_h2[1].hdr_type = 8w2;
                                  hdr_1_h2[1].f1 = 8w0xa1;
--- 323,329 ----
                              hdr_1_h2[0].next_hdr_type = 8w9;
                          }
                          else 
!                             if (hdr.h1.op3[3:0] == 4w1) {
                                  hdr_1_h2[1].setValid();
                                  hdr_1_h2[1].hdr_type = 8w2;
                                  hdr_1_h2[1].f1 = 8w0xa1;
*************** control cIngress(inout headers hdr, inou
*** 379,385 ****
                                  hdr_1_h2[1].next_hdr_type = 8w9;
                              }
                              else 
!                                 if (op[3:0] == 4w2) {
                                      hdr_1_h2[2].setValid();
                                      hdr_1_h2[2].hdr_type = 8w2;
                                      hdr_1_h2[2].f1 = 8w0xa2;
--- 331,337 ----
                                  hdr_1_h2[1].next_hdr_type = 8w9;
                              }
                              else 
!                                 if (hdr.h1.op3[3:0] == 4w2) {
                                      hdr_1_h2[2].setValid();
                                      hdr_1_h2[2].hdr_type = 8w2;
                                      hdr_1_h2[2].f1 = 8w0xa2;
*************** control cIngress(inout headers hdr, inou
*** 387,393 ****
                                      hdr_1_h2[2].next_hdr_type = 8w9;
                                  }
                                  else 
!                                     if (op[3:0] == 4w3) {
                                          hdr_1_h2[3].setValid();
                                          hdr_1_h2[3].hdr_type = 8w2;
                                          hdr_1_h2[3].f1 = 8w0xa3;
--- 339,345 ----
                                      hdr_1_h2[2].next_hdr_type = 8w9;
                                  }
                                  else 
!                                     if (hdr.h1.op3[3:0] == 4w3) {
                                          hdr_1_h2[3].setValid();
                                          hdr_1_h2[3].hdr_type = 8w2;
                                          hdr_1_h2[3].f1 = 8w0xa3;
*************** control cIngress(inout headers hdr, inou
*** 395,401 ****
                                          hdr_1_h2[3].next_hdr_type = 8w9;
                                      }
                                      else 
!                                         if (op[3:0] == 4w4) {
                                              hdr_1_h2[4].setValid();
                                              hdr_1_h2[4].hdr_type = 8w2;
                                              hdr_1_h2[4].f1 = 8w0xa4;
--- 347,353 ----
                                          hdr_1_h2[3].next_hdr_type = 8w9;
                                      }
                                      else 
!                                         if (hdr.h1.op3[3:0] == 4w4) {
                                              hdr_1_h2[4].setValid();
                                              hdr_1_h2[4].hdr_type = 8w2;
                                              hdr_1_h2[4].f1 = 8w0xa4;
*************** control cIngress(inout headers hdr, inou
*** 403,432 ****
                                              hdr_1_h2[4].next_hdr_type = 8w9;
                                          }
                      else 
!                         if (op[7:4] == 4w4) 
!                             if (op[3:0] == 4w0) 
                                  hdr_1_h2[0].setInvalid();
                              else 
!                                 if (op[3:0] == 4w1) 
                                      hdr_1_h2[1].setInvalid();
                                  else 
!                                     if (op[3:0] == 4w2) 
                                          hdr_1_h2[2].setInvalid();
                                      else 
!                                         if (op[3:0] == 4w3) 
                                              hdr_1_h2[3].setInvalid();
                                          else 
!                                             if (op[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
          {
-             tmp_9_h1 = hdr_1_h1;
-             tmp_9_h2 = hdr_1_h2;
-             tmp_9_h3 = hdr_1_h3;
          }
          {
!             hdr.h1 = tmp_9_h1;
!             hdr.h2 = tmp_9_h2;
!             hdr.h3 = tmp_9_h3;
          }
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
--- 355,379 ----
                                              hdr_1_h2[4].next_hdr_type = 8w9;
                                          }
                      else 
!                         if (hdr.h1.op3[7:4] == 4w4) 
!                             if (hdr.h1.op3[3:0] == 4w0) 
                                  hdr_1_h2[0].setInvalid();
                              else 
!                                 if (hdr.h1.op3[3:0] == 4w1) 
                                      hdr_1_h2[1].setInvalid();
                                  else 
!                                     if (hdr.h1.op3[3:0] == 4w2) 
                                          hdr_1_h2[2].setInvalid();
                                      else 
!                                         if (hdr.h1.op3[3:0] == 4w3) 
                                              hdr_1_h2[3].setInvalid();
                                          else 
!                                             if (hdr.h1.op3[3:0] == 4w4) 
                                                  hdr_1_h2[4].setInvalid();
          {
          }
          {
!             hdr.h2 = hdr_1_h2;
          }
          hdr.h1.h2_valid_bits = 8w0;
          if (hdr.h2[0].isValid()) 
