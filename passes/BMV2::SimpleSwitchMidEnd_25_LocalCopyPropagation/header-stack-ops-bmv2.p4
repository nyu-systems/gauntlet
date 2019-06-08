--- dumps/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:46.272197800 +0200
+++ dumps/pruned/header-stack-ops-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:46.277445400 +0200
@@ -54,78 +54,56 @@ parser parserI(packet_in pkt, out header
     }
 }
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
-    h1_t tmp_5_h1;
-    h2_t[5] tmp_5_h2;
-    h3_t tmp_5_h3;
-    bit<8> tmp_6;
-    h1_t tmp_7_h1;
-    h2_t[5] tmp_7_h2;
-    h3_t tmp_7_h3;
-    bit<8> tmp_8;
-    h1_t tmp_9_h1;
-    h2_t[5] tmp_9_h2;
-    h3_t tmp_9_h3;
-    bit<8> tmp_10;
-    h1_t hdr_1_h1;
     h2_t[5] hdr_1_h2;
-    h3_t hdr_1_h3;
-    bit<8> op;
     apply {
         {
-            tmp_5_h1 = hdr.h1;
-            tmp_5_h2 = hdr.h2;
-            tmp_5_h3 = hdr.h3;
-        }
-        tmp_6 = hdr.h1.op1;
-        {
-            hdr_1_h1 = tmp_5_h1;
-            hdr_1_h2 = tmp_5_h2;
-            hdr_1_h3 = tmp_5_h3;
         }
-        op = tmp_6;
-        if (op == 8w0x0) 
+        {
+            hdr_1_h2 = hdr.h2;
+        }
+        if (hdr.h1.op1 == 8w0x0) 
             ;
         else 
-            if (op[7:4] == 4w1) 
-                if (op[3:0] == 4w1) 
+            if (hdr.h1.op1[7:4] == 4w1) 
+                if (hdr.h1.op1[3:0] == 4w1) 
                     hdr_1_h2.push_front(1);
                 else 
-                    if (op[3:0] == 4w2) 
+                    if (hdr.h1.op1[3:0] == 4w2) 
                         hdr_1_h2.push_front(2);
                     else 
-                        if (op[3:0] == 4w3) 
+                        if (hdr.h1.op1[3:0] == 4w3) 
                             hdr_1_h2.push_front(3);
                         else 
-                            if (op[3:0] == 4w4) 
+                            if (hdr.h1.op1[3:0] == 4w4) 
                                 hdr_1_h2.push_front(4);
                             else 
-                                if (op[3:0] == 4w5) 
+                                if (hdr.h1.op1[3:0] == 4w5) 
                                     hdr_1_h2.push_front(5);
                                 else 
-                                    if (op[3:0] == 4w6) 
+                                    if (hdr.h1.op1[3:0] == 4w6) 
                                         hdr_1_h2.push_front(6);
             else 
-                if (op[7:4] == 4w2) 
-                    if (op[3:0] == 4w1) 
+                if (hdr.h1.op1[7:4] == 4w2) 
+                    if (hdr.h1.op1[3:0] == 4w1) 
                         hdr_1_h2.pop_front(1);
                     else 
-                        if (op[3:0] == 4w2) 
+                        if (hdr.h1.op1[3:0] == 4w2) 
                             hdr_1_h2.pop_front(2);
                         else 
-                            if (op[3:0] == 4w3) 
+                            if (hdr.h1.op1[3:0] == 4w3) 
                                 hdr_1_h2.pop_front(3);
                             else 
-                                if (op[3:0] == 4w4) 
+                                if (hdr.h1.op1[3:0] == 4w4) 
                                     hdr_1_h2.pop_front(4);
                                 else 
-                                    if (op[3:0] == 4w5) 
+                                    if (hdr.h1.op1[3:0] == 4w5) 
                                         hdr_1_h2.pop_front(5);
                                     else 
-                                        if (op[3:0] == 4w6) 
+                                        if (hdr.h1.op1[3:0] == 4w6) 
                                             hdr_1_h2.pop_front(6);
                 else 
-                    if (op[7:4] == 4w3) 
-                        if (op[3:0] == 4w0) {
+                    if (hdr.h1.op1[7:4] == 4w3) 
+                        if (hdr.h1.op1[3:0] == 4w0) {
                             hdr_1_h2[0].setValid();
                             hdr_1_h2[0].hdr_type = 8w2;
                             hdr_1_h2[0].f1 = 8w0xa0;
@@ -133,7 +111,7 @@ control cIngress(inout headers hdr, inou
                             hdr_1_h2[0].next_hdr_type = 8w9;
                         }
                         else 
-                            if (op[3:0] == 4w1) {
+                            if (hdr.h1.op1[3:0] == 4w1) {
                                 hdr_1_h2[1].setValid();
                                 hdr_1_h2[1].hdr_type = 8w2;
                                 hdr_1_h2[1].f1 = 8w0xa1;
@@ -141,7 +119,7 @@ control cIngress(inout headers hdr, inou
                                 hdr_1_h2[1].next_hdr_type = 8w9;
                             }
                             else 
-                                if (op[3:0] == 4w2) {
+                                if (hdr.h1.op1[3:0] == 4w2) {
                                     hdr_1_h2[2].setValid();
                                     hdr_1_h2[2].hdr_type = 8w2;
                                     hdr_1_h2[2].f1 = 8w0xa2;
@@ -149,7 +127,7 @@ control cIngress(inout headers hdr, inou
                                     hdr_1_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
-                                    if (op[3:0] == 4w3) {
+                                    if (hdr.h1.op1[3:0] == 4w3) {
                                         hdr_1_h2[3].setValid();
                                         hdr_1_h2[3].hdr_type = 8w2;
                                         hdr_1_h2[3].f1 = 8w0xa3;
@@ -157,7 +135,7 @@ control cIngress(inout headers hdr, inou
                                         hdr_1_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
-                                        if (op[3:0] == 4w4) {
+                                        if (hdr.h1.op1[3:0] == 4w4) {
                                             hdr_1_h2[4].setValid();
                                             hdr_1_h2[4].hdr_type = 8w2;
                                             hdr_1_h2[4].f1 = 8w0xa4;
@@ -165,86 +143,73 @@ control cIngress(inout headers hdr, inou
                                             hdr_1_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
-                        if (op[7:4] == 4w4) 
-                            if (op[3:0] == 4w0) 
+                        if (hdr.h1.op1[7:4] == 4w4) 
+                            if (hdr.h1.op1[3:0] == 4w0) 
                                 hdr_1_h2[0].setInvalid();
                             else 
-                                if (op[3:0] == 4w1) 
+                                if (hdr.h1.op1[3:0] == 4w1) 
                                     hdr_1_h2[1].setInvalid();
                                 else 
-                                    if (op[3:0] == 4w2) 
+                                    if (hdr.h1.op1[3:0] == 4w2) 
                                         hdr_1_h2[2].setInvalid();
                                     else 
-                                        if (op[3:0] == 4w3) 
+                                        if (hdr.h1.op1[3:0] == 4w3) 
                                             hdr_1_h2[3].setInvalid();
                                         else 
-                                            if (op[3:0] == 4w4) 
+                                            if (hdr.h1.op1[3:0] == 4w4) 
                                                 hdr_1_h2[4].setInvalid();
         {
-            tmp_5_h1 = hdr_1_h1;
-            tmp_5_h2 = hdr_1_h2;
-            tmp_5_h3 = hdr_1_h3;
         }
         {
-            hdr.h1 = tmp_5_h1;
-            hdr.h2 = tmp_5_h2;
-            hdr.h3 = tmp_5_h3;
+            hdr.h2 = hdr_1_h2;
         }
         {
-            tmp_7_h1 = hdr.h1;
-            tmp_7_h2 = hdr.h2;
-            tmp_7_h3 = hdr.h3;
         }
-        tmp_8 = hdr.h1.op2;
         {
-            hdr_1_h1 = tmp_7_h1;
-            hdr_1_h2 = tmp_7_h2;
-            hdr_1_h3 = tmp_7_h3;
         }
-        op = tmp_8;
-        if (op == 8w0x0) 
+        if (hdr.h1.op2 == 8w0x0) 
             ;
         else 
-            if (op[7:4] == 4w1) 
-                if (op[3:0] == 4w1) 
+            if (hdr.h1.op2[7:4] == 4w1) 
+                if (hdr.h1.op2[3:0] == 4w1) 
                     hdr_1_h2.push_front(1);
                 else 
-                    if (op[3:0] == 4w2) 
+                    if (hdr.h1.op2[3:0] == 4w2) 
                         hdr_1_h2.push_front(2);
                     else 
-                        if (op[3:0] == 4w3) 
+                        if (hdr.h1.op2[3:0] == 4w3) 
                             hdr_1_h2.push_front(3);
                         else 
-                            if (op[3:0] == 4w4) 
+                            if (hdr.h1.op2[3:0] == 4w4) 
                                 hdr_1_h2.push_front(4);
                             else 
-                                if (op[3:0] == 4w5) 
+                                if (hdr.h1.op2[3:0] == 4w5) 
                                     hdr_1_h2.push_front(5);
                                 else 
-                                    if (op[3:0] == 4w6) 
+                                    if (hdr.h1.op2[3:0] == 4w6) 
                                         hdr_1_h2.push_front(6);
             else 
-                if (op[7:4] == 4w2) 
-                    if (op[3:0] == 4w1) 
+                if (hdr.h1.op2[7:4] == 4w2) 
+                    if (hdr.h1.op2[3:0] == 4w1) 
                         hdr_1_h2.pop_front(1);
                     else 
-                        if (op[3:0] == 4w2) 
+                        if (hdr.h1.op2[3:0] == 4w2) 
                             hdr_1_h2.pop_front(2);
                         else 
-                            if (op[3:0] == 4w3) 
+                            if (hdr.h1.op2[3:0] == 4w3) 
                                 hdr_1_h2.pop_front(3);
                             else 
-                                if (op[3:0] == 4w4) 
+                                if (hdr.h1.op2[3:0] == 4w4) 
                                     hdr_1_h2.pop_front(4);
                                 else 
-                                    if (op[3:0] == 4w5) 
+                                    if (hdr.h1.op2[3:0] == 4w5) 
                                         hdr_1_h2.pop_front(5);
                                     else 
-                                        if (op[3:0] == 4w6) 
+                                        if (hdr.h1.op2[3:0] == 4w6) 
                                             hdr_1_h2.pop_front(6);
                 else 
-                    if (op[7:4] == 4w3) 
-                        if (op[3:0] == 4w0) {
+                    if (hdr.h1.op2[7:4] == 4w3) 
+                        if (hdr.h1.op2[3:0] == 4w0) {
                             hdr_1_h2[0].setValid();
                             hdr_1_h2[0].hdr_type = 8w2;
                             hdr_1_h2[0].f1 = 8w0xa0;
@@ -252,7 +217,7 @@ control cIngress(inout headers hdr, inou
                             hdr_1_h2[0].next_hdr_type = 8w9;
                         }
                         else 
-                            if (op[3:0] == 4w1) {
+                            if (hdr.h1.op2[3:0] == 4w1) {
                                 hdr_1_h2[1].setValid();
                                 hdr_1_h2[1].hdr_type = 8w2;
                                 hdr_1_h2[1].f1 = 8w0xa1;
@@ -260,7 +225,7 @@ control cIngress(inout headers hdr, inou
                                 hdr_1_h2[1].next_hdr_type = 8w9;
                             }
                             else 
-                                if (op[3:0] == 4w2) {
+                                if (hdr.h1.op2[3:0] == 4w2) {
                                     hdr_1_h2[2].setValid();
                                     hdr_1_h2[2].hdr_type = 8w2;
                                     hdr_1_h2[2].f1 = 8w0xa2;
@@ -268,7 +233,7 @@ control cIngress(inout headers hdr, inou
                                     hdr_1_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
-                                    if (op[3:0] == 4w3) {
+                                    if (hdr.h1.op2[3:0] == 4w3) {
                                         hdr_1_h2[3].setValid();
                                         hdr_1_h2[3].hdr_type = 8w2;
                                         hdr_1_h2[3].f1 = 8w0xa3;
@@ -276,7 +241,7 @@ control cIngress(inout headers hdr, inou
                                         hdr_1_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
-                                        if (op[3:0] == 4w4) {
+                                        if (hdr.h1.op2[3:0] == 4w4) {
                                             hdr_1_h2[4].setValid();
                                             hdr_1_h2[4].hdr_type = 8w2;
                                             hdr_1_h2[4].f1 = 8w0xa4;
@@ -284,86 +249,73 @@ control cIngress(inout headers hdr, inou
                                             hdr_1_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
-                        if (op[7:4] == 4w4) 
-                            if (op[3:0] == 4w0) 
+                        if (hdr.h1.op2[7:4] == 4w4) 
+                            if (hdr.h1.op2[3:0] == 4w0) 
                                 hdr_1_h2[0].setInvalid();
                             else 
-                                if (op[3:0] == 4w1) 
+                                if (hdr.h1.op2[3:0] == 4w1) 
                                     hdr_1_h2[1].setInvalid();
                                 else 
-                                    if (op[3:0] == 4w2) 
+                                    if (hdr.h1.op2[3:0] == 4w2) 
                                         hdr_1_h2[2].setInvalid();
                                     else 
-                                        if (op[3:0] == 4w3) 
+                                        if (hdr.h1.op2[3:0] == 4w3) 
                                             hdr_1_h2[3].setInvalid();
                                         else 
-                                            if (op[3:0] == 4w4) 
+                                            if (hdr.h1.op2[3:0] == 4w4) 
                                                 hdr_1_h2[4].setInvalid();
         {
-            tmp_7_h1 = hdr_1_h1;
-            tmp_7_h2 = hdr_1_h2;
-            tmp_7_h3 = hdr_1_h3;
         }
         {
-            hdr.h1 = tmp_7_h1;
-            hdr.h2 = tmp_7_h2;
-            hdr.h3 = tmp_7_h3;
+            hdr.h2 = hdr_1_h2;
         }
         {
-            tmp_9_h1 = hdr.h1;
-            tmp_9_h2 = hdr.h2;
-            tmp_9_h3 = hdr.h3;
         }
-        tmp_10 = hdr.h1.op3;
         {
-            hdr_1_h1 = tmp_9_h1;
-            hdr_1_h2 = tmp_9_h2;
-            hdr_1_h3 = tmp_9_h3;
         }
-        op = tmp_10;
-        if (op == 8w0x0) 
+        if (hdr.h1.op3 == 8w0x0) 
             ;
         else 
-            if (op[7:4] == 4w1) 
-                if (op[3:0] == 4w1) 
+            if (hdr.h1.op3[7:4] == 4w1) 
+                if (hdr.h1.op3[3:0] == 4w1) 
                     hdr_1_h2.push_front(1);
                 else 
-                    if (op[3:0] == 4w2) 
+                    if (hdr.h1.op3[3:0] == 4w2) 
                         hdr_1_h2.push_front(2);
                     else 
-                        if (op[3:0] == 4w3) 
+                        if (hdr.h1.op3[3:0] == 4w3) 
                             hdr_1_h2.push_front(3);
                         else 
-                            if (op[3:0] == 4w4) 
+                            if (hdr.h1.op3[3:0] == 4w4) 
                                 hdr_1_h2.push_front(4);
                             else 
-                                if (op[3:0] == 4w5) 
+                                if (hdr.h1.op3[3:0] == 4w5) 
                                     hdr_1_h2.push_front(5);
                                 else 
-                                    if (op[3:0] == 4w6) 
+                                    if (hdr.h1.op3[3:0] == 4w6) 
                                         hdr_1_h2.push_front(6);
             else 
-                if (op[7:4] == 4w2) 
-                    if (op[3:0] == 4w1) 
+                if (hdr.h1.op3[7:4] == 4w2) 
+                    if (hdr.h1.op3[3:0] == 4w1) 
                         hdr_1_h2.pop_front(1);
                     else 
-                        if (op[3:0] == 4w2) 
+                        if (hdr.h1.op3[3:0] == 4w2) 
                             hdr_1_h2.pop_front(2);
                         else 
-                            if (op[3:0] == 4w3) 
+                            if (hdr.h1.op3[3:0] == 4w3) 
                                 hdr_1_h2.pop_front(3);
                             else 
-                                if (op[3:0] == 4w4) 
+                                if (hdr.h1.op3[3:0] == 4w4) 
                                     hdr_1_h2.pop_front(4);
                                 else 
-                                    if (op[3:0] == 4w5) 
+                                    if (hdr.h1.op3[3:0] == 4w5) 
                                         hdr_1_h2.pop_front(5);
                                     else 
-                                        if (op[3:0] == 4w6) 
+                                        if (hdr.h1.op3[3:0] == 4w6) 
                                             hdr_1_h2.pop_front(6);
                 else 
-                    if (op[7:4] == 4w3) 
-                        if (op[3:0] == 4w0) {
+                    if (hdr.h1.op3[7:4] == 4w3) 
+                        if (hdr.h1.op3[3:0] == 4w0) {
                             hdr_1_h2[0].setValid();
                             hdr_1_h2[0].hdr_type = 8w2;
                             hdr_1_h2[0].f1 = 8w0xa0;
@@ -371,7 +323,7 @@ control cIngress(inout headers hdr, inou
                             hdr_1_h2[0].next_hdr_type = 8w9;
                         }
                         else 
-                            if (op[3:0] == 4w1) {
+                            if (hdr.h1.op3[3:0] == 4w1) {
                                 hdr_1_h2[1].setValid();
                                 hdr_1_h2[1].hdr_type = 8w2;
                                 hdr_1_h2[1].f1 = 8w0xa1;
@@ -379,7 +331,7 @@ control cIngress(inout headers hdr, inou
                                 hdr_1_h2[1].next_hdr_type = 8w9;
                             }
                             else 
-                                if (op[3:0] == 4w2) {
+                                if (hdr.h1.op3[3:0] == 4w2) {
                                     hdr_1_h2[2].setValid();
                                     hdr_1_h2[2].hdr_type = 8w2;
                                     hdr_1_h2[2].f1 = 8w0xa2;
@@ -387,7 +339,7 @@ control cIngress(inout headers hdr, inou
                                     hdr_1_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
-                                    if (op[3:0] == 4w3) {
+                                    if (hdr.h1.op3[3:0] == 4w3) {
                                         hdr_1_h2[3].setValid();
                                         hdr_1_h2[3].hdr_type = 8w2;
                                         hdr_1_h2[3].f1 = 8w0xa3;
@@ -395,7 +347,7 @@ control cIngress(inout headers hdr, inou
                                         hdr_1_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
-                                        if (op[3:0] == 4w4) {
+                                        if (hdr.h1.op3[3:0] == 4w4) {
                                             hdr_1_h2[4].setValid();
                                             hdr_1_h2[4].hdr_type = 8w2;
                                             hdr_1_h2[4].f1 = 8w0xa4;
@@ -403,30 +355,25 @@ control cIngress(inout headers hdr, inou
                                             hdr_1_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
-                        if (op[7:4] == 4w4) 
-                            if (op[3:0] == 4w0) 
+                        if (hdr.h1.op3[7:4] == 4w4) 
+                            if (hdr.h1.op3[3:0] == 4w0) 
                                 hdr_1_h2[0].setInvalid();
                             else 
-                                if (op[3:0] == 4w1) 
+                                if (hdr.h1.op3[3:0] == 4w1) 
                                     hdr_1_h2[1].setInvalid();
                                 else 
-                                    if (op[3:0] == 4w2) 
+                                    if (hdr.h1.op3[3:0] == 4w2) 
                                         hdr_1_h2[2].setInvalid();
                                     else 
-                                        if (op[3:0] == 4w3) 
+                                        if (hdr.h1.op3[3:0] == 4w3) 
                                             hdr_1_h2[3].setInvalid();
                                         else 
-                                            if (op[3:0] == 4w4) 
+                                            if (hdr.h1.op3[3:0] == 4w4) 
                                                 hdr_1_h2[4].setInvalid();
         {
-            tmp_9_h1 = hdr_1_h1;
-            tmp_9_h2 = hdr_1_h2;
-            tmp_9_h3 = hdr_1_h3;
         }
         {
-            hdr.h1 = tmp_9_h1;
-            hdr.h2 = tmp_9_h2;
-            hdr.h3 = tmp_9_h3;
+            hdr.h2 = hdr_1_h2;
         }
         hdr.h1.h2_valid_bits = 8w0;
         if (hdr.h2[0].isValid()) 
