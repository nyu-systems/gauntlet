--- before_pass
+++ after_pass
@@ -54,78 +54,54 @@ parser parserI(packet_in pkt, out header
     }
 }
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
-    h1_t tmp_h1;
-    h2_t[5] tmp_h2;
-    h3_t tmp_h3;
-    bit<8> tmp_0;
-    h1_t tmp_1_h1;
-    h2_t[5] tmp_1_h2;
-    h3_t tmp_1_h3;
-    bit<8> tmp_2;
-    h1_t tmp_3_h1;
-    h2_t[5] tmp_3_h2;
-    h3_t tmp_3_h3;
-    bit<8> tmp_4;
-    h1_t hdr_0_h1;
     h2_t[5] hdr_0_h2;
-    h3_t hdr_0_h3;
-    bit<8> op_0;
     apply {
         {
-            tmp_h1 = hdr.h1;
-            tmp_h2 = hdr.h2;
-            tmp_h3 = hdr.h3;
+            hdr_0_h2 = hdr.h2;
         }
-        tmp_0 = hdr.h1.op1;
-        {
-            hdr_0_h1 = tmp_h1;
-            hdr_0_h2 = tmp_h2;
-            hdr_0_h3 = tmp_h3;
-        }
-        op_0 = tmp_0;
-        if (op_0 == 8w0x0) 
+        if (hdr.h1.op1 == 8w0x0) 
             ;
         else 
-            if (op_0[7:4] == 4w1) 
-                if (op_0[3:0] == 4w1) 
+            if (hdr.h1.op1[7:4] == 4w1) 
+                if (hdr.h1.op1[3:0] == 4w1) 
                     hdr_0_h2.push_front(1);
                 else 
-                    if (op_0[3:0] == 4w2) 
+                    if (hdr.h1.op1[3:0] == 4w2) 
                         hdr_0_h2.push_front(2);
                     else 
-                        if (op_0[3:0] == 4w3) 
+                        if (hdr.h1.op1[3:0] == 4w3) 
                             hdr_0_h2.push_front(3);
                         else 
-                            if (op_0[3:0] == 4w4) 
+                            if (hdr.h1.op1[3:0] == 4w4) 
                                 hdr_0_h2.push_front(4);
                             else 
-                                if (op_0[3:0] == 4w5) 
+                                if (hdr.h1.op1[3:0] == 4w5) 
                                     hdr_0_h2.push_front(5);
                                 else 
-                                    if (op_0[3:0] == 4w6) 
+                                    if (hdr.h1.op1[3:0] == 4w6) 
                                         hdr_0_h2.push_front(6);
             else 
-                if (op_0[7:4] == 4w2) 
-                    if (op_0[3:0] == 4w1) 
+                if (hdr.h1.op1[7:4] == 4w2) 
+                    if (hdr.h1.op1[3:0] == 4w1) 
                         hdr_0_h2.pop_front(1);
                     else 
-                        if (op_0[3:0] == 4w2) 
+                        if (hdr.h1.op1[3:0] == 4w2) 
                             hdr_0_h2.pop_front(2);
                         else 
-                            if (op_0[3:0] == 4w3) 
+                            if (hdr.h1.op1[3:0] == 4w3) 
                                 hdr_0_h2.pop_front(3);
                             else 
-                                if (op_0[3:0] == 4w4) 
+                                if (hdr.h1.op1[3:0] == 4w4) 
                                     hdr_0_h2.pop_front(4);
                                 else 
-                                    if (op_0[3:0] == 4w5) 
+                                    if (hdr.h1.op1[3:0] == 4w5) 
                                         hdr_0_h2.pop_front(5);
                                     else 
-                                        if (op_0[3:0] == 4w6) 
+                                        if (hdr.h1.op1[3:0] == 4w6) 
                                             hdr_0_h2.pop_front(6);
                 else 
-                    if (op_0[7:4] == 4w3) 
-                        if (op_0[3:0] == 4w0) {
+                    if (hdr.h1.op1[7:4] == 4w3) 
+                        if (hdr.h1.op1[3:0] == 4w0) {
                             hdr_0_h2[0].setValid();
                             hdr_0_h2[0].hdr_type = 8w2;
                             hdr_0_h2[0].f1 = 8w0xa0;
@@ -133,7 +109,7 @@ control cIngress(inout headers hdr, inou
                             hdr_0_h2[0].next_hdr_type = 8w9;
                         }
                         else 
-                            if (op_0[3:0] == 4w1) {
+                            if (hdr.h1.op1[3:0] == 4w1) {
                                 hdr_0_h2[1].setValid();
                                 hdr_0_h2[1].hdr_type = 8w2;
                                 hdr_0_h2[1].f1 = 8w0xa1;
@@ -141,7 +117,7 @@ control cIngress(inout headers hdr, inou
                                 hdr_0_h2[1].next_hdr_type = 8w9;
                             }
                             else 
-                                if (op_0[3:0] == 4w2) {
+                                if (hdr.h1.op1[3:0] == 4w2) {
                                     hdr_0_h2[2].setValid();
                                     hdr_0_h2[2].hdr_type = 8w2;
                                     hdr_0_h2[2].f1 = 8w0xa2;
@@ -149,7 +125,7 @@ control cIngress(inout headers hdr, inou
                                     hdr_0_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
-                                    if (op_0[3:0] == 4w3) {
+                                    if (hdr.h1.op1[3:0] == 4w3) {
                                         hdr_0_h2[3].setValid();
                                         hdr_0_h2[3].hdr_type = 8w2;
                                         hdr_0_h2[3].f1 = 8w0xa3;
@@ -157,7 +133,7 @@ control cIngress(inout headers hdr, inou
                                         hdr_0_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
-                                        if (op_0[3:0] == 4w4) {
+                                        if (hdr.h1.op1[3:0] == 4w4) {
                                             hdr_0_h2[4].setValid();
                                             hdr_0_h2[4].hdr_type = 8w2;
                                             hdr_0_h2[4].f1 = 8w0xa4;
@@ -165,86 +141,67 @@ control cIngress(inout headers hdr, inou
                                             hdr_0_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
-                        if (op_0[7:4] == 4w4) 
-                            if (op_0[3:0] == 4w0) 
+                        if (hdr.h1.op1[7:4] == 4w4) 
+                            if (hdr.h1.op1[3:0] == 4w0) 
                                 hdr_0_h2[0].setInvalid();
                             else 
-                                if (op_0[3:0] == 4w1) 
+                                if (hdr.h1.op1[3:0] == 4w1) 
                                     hdr_0_h2[1].setInvalid();
                                 else 
-                                    if (op_0[3:0] == 4w2) 
+                                    if (hdr.h1.op1[3:0] == 4w2) 
                                         hdr_0_h2[2].setInvalid();
                                     else 
-                                        if (op_0[3:0] == 4w3) 
+                                        if (hdr.h1.op1[3:0] == 4w3) 
                                             hdr_0_h2[3].setInvalid();
                                         else 
-                                            if (op_0[3:0] == 4w4) 
+                                            if (hdr.h1.op1[3:0] == 4w4) 
                                                 hdr_0_h2[4].setInvalid();
         {
-            tmp_h1 = hdr_0_h1;
-            tmp_h2 = hdr_0_h2;
-            tmp_h3 = hdr_0_h3;
-        }
-        {
-            hdr.h1 = tmp_h1;
-            hdr.h2 = tmp_h2;
-            hdr.h3 = tmp_h3;
-        }
-        {
-            tmp_1_h1 = hdr.h1;
-            tmp_1_h2 = hdr.h2;
-            tmp_1_h3 = hdr.h3;
-        }
-        tmp_2 = hdr.h1.op2;
-        {
-            hdr_0_h1 = tmp_1_h1;
-            hdr_0_h2 = tmp_1_h2;
-            hdr_0_h3 = tmp_1_h3;
+            hdr.h2 = hdr_0_h2;
         }
-        op_0 = tmp_2;
-        if (op_0 == 8w0x0) 
+        if (hdr.h1.op2 == 8w0x0) 
             ;
         else 
-            if (op_0[7:4] == 4w1) 
-                if (op_0[3:0] == 4w1) 
+            if (hdr.h1.op2[7:4] == 4w1) 
+                if (hdr.h1.op2[3:0] == 4w1) 
                     hdr_0_h2.push_front(1);
                 else 
-                    if (op_0[3:0] == 4w2) 
+                    if (hdr.h1.op2[3:0] == 4w2) 
                         hdr_0_h2.push_front(2);
                     else 
-                        if (op_0[3:0] == 4w3) 
+                        if (hdr.h1.op2[3:0] == 4w3) 
                             hdr_0_h2.push_front(3);
                         else 
-                            if (op_0[3:0] == 4w4) 
+                            if (hdr.h1.op2[3:0] == 4w4) 
                                 hdr_0_h2.push_front(4);
                             else 
-                                if (op_0[3:0] == 4w5) 
+                                if (hdr.h1.op2[3:0] == 4w5) 
                                     hdr_0_h2.push_front(5);
                                 else 
-                                    if (op_0[3:0] == 4w6) 
+                                    if (hdr.h1.op2[3:0] == 4w6) 
                                         hdr_0_h2.push_front(6);
             else 
-                if (op_0[7:4] == 4w2) 
-                    if (op_0[3:0] == 4w1) 
+                if (hdr.h1.op2[7:4] == 4w2) 
+                    if (hdr.h1.op2[3:0] == 4w1) 
                         hdr_0_h2.pop_front(1);
                     else 
-                        if (op_0[3:0] == 4w2) 
+                        if (hdr.h1.op2[3:0] == 4w2) 
                             hdr_0_h2.pop_front(2);
                         else 
-                            if (op_0[3:0] == 4w3) 
+                            if (hdr.h1.op2[3:0] == 4w3) 
                                 hdr_0_h2.pop_front(3);
                             else 
-                                if (op_0[3:0] == 4w4) 
+                                if (hdr.h1.op2[3:0] == 4w4) 
                                     hdr_0_h2.pop_front(4);
                                 else 
-                                    if (op_0[3:0] == 4w5) 
+                                    if (hdr.h1.op2[3:0] == 4w5) 
                                         hdr_0_h2.pop_front(5);
                                     else 
-                                        if (op_0[3:0] == 4w6) 
+                                        if (hdr.h1.op2[3:0] == 4w6) 
                                             hdr_0_h2.pop_front(6);
                 else 
-                    if (op_0[7:4] == 4w3) 
-                        if (op_0[3:0] == 4w0) {
+                    if (hdr.h1.op2[7:4] == 4w3) 
+                        if (hdr.h1.op2[3:0] == 4w0) {
                             hdr_0_h2[0].setValid();
                             hdr_0_h2[0].hdr_type = 8w2;
                             hdr_0_h2[0].f1 = 8w0xa0;
@@ -252,7 +209,7 @@ control cIngress(inout headers hdr, inou
                             hdr_0_h2[0].next_hdr_type = 8w9;
                         }
                         else 
-                            if (op_0[3:0] == 4w1) {
+                            if (hdr.h1.op2[3:0] == 4w1) {
                                 hdr_0_h2[1].setValid();
                                 hdr_0_h2[1].hdr_type = 8w2;
                                 hdr_0_h2[1].f1 = 8w0xa1;
@@ -260,7 +217,7 @@ control cIngress(inout headers hdr, inou
                                 hdr_0_h2[1].next_hdr_type = 8w9;
                             }
                             else 
-                                if (op_0[3:0] == 4w2) {
+                                if (hdr.h1.op2[3:0] == 4w2) {
                                     hdr_0_h2[2].setValid();
                                     hdr_0_h2[2].hdr_type = 8w2;
                                     hdr_0_h2[2].f1 = 8w0xa2;
@@ -268,7 +225,7 @@ control cIngress(inout headers hdr, inou
                                     hdr_0_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
-                                    if (op_0[3:0] == 4w3) {
+                                    if (hdr.h1.op2[3:0] == 4w3) {
                                         hdr_0_h2[3].setValid();
                                         hdr_0_h2[3].hdr_type = 8w2;
                                         hdr_0_h2[3].f1 = 8w0xa3;
@@ -276,7 +233,7 @@ control cIngress(inout headers hdr, inou
                                         hdr_0_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
-                                        if (op_0[3:0] == 4w4) {
+                                        if (hdr.h1.op2[3:0] == 4w4) {
                                             hdr_0_h2[4].setValid();
                                             hdr_0_h2[4].hdr_type = 8w2;
                                             hdr_0_h2[4].f1 = 8w0xa4;
@@ -284,86 +241,67 @@ control cIngress(inout headers hdr, inou
                                             hdr_0_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
-                        if (op_0[7:4] == 4w4) 
-                            if (op_0[3:0] == 4w0) 
+                        if (hdr.h1.op2[7:4] == 4w4) 
+                            if (hdr.h1.op2[3:0] == 4w0) 
                                 hdr_0_h2[0].setInvalid();
                             else 
-                                if (op_0[3:0] == 4w1) 
+                                if (hdr.h1.op2[3:0] == 4w1) 
                                     hdr_0_h2[1].setInvalid();
                                 else 
-                                    if (op_0[3:0] == 4w2) 
+                                    if (hdr.h1.op2[3:0] == 4w2) 
                                         hdr_0_h2[2].setInvalid();
                                     else 
-                                        if (op_0[3:0] == 4w3) 
+                                        if (hdr.h1.op2[3:0] == 4w3) 
                                             hdr_0_h2[3].setInvalid();
                                         else 
-                                            if (op_0[3:0] == 4w4) 
+                                            if (hdr.h1.op2[3:0] == 4w4) 
                                                 hdr_0_h2[4].setInvalid();
         {
-            tmp_1_h1 = hdr_0_h1;
-            tmp_1_h2 = hdr_0_h2;
-            tmp_1_h3 = hdr_0_h3;
+            hdr.h2 = hdr_0_h2;
         }
-        {
-            hdr.h1 = tmp_1_h1;
-            hdr.h2 = tmp_1_h2;
-            hdr.h3 = tmp_1_h3;
-        }
-        {
-            tmp_3_h1 = hdr.h1;
-            tmp_3_h2 = hdr.h2;
-            tmp_3_h3 = hdr.h3;
-        }
-        tmp_4 = hdr.h1.op3;
-        {
-            hdr_0_h1 = tmp_3_h1;
-            hdr_0_h2 = tmp_3_h2;
-            hdr_0_h3 = tmp_3_h3;
-        }
-        op_0 = tmp_4;
-        if (op_0 == 8w0x0) 
+        if (hdr.h1.op3 == 8w0x0) 
             ;
         else 
-            if (op_0[7:4] == 4w1) 
-                if (op_0[3:0] == 4w1) 
+            if (hdr.h1.op3[7:4] == 4w1) 
+                if (hdr.h1.op3[3:0] == 4w1) 
                     hdr_0_h2.push_front(1);
                 else 
-                    if (op_0[3:0] == 4w2) 
+                    if (hdr.h1.op3[3:0] == 4w2) 
                         hdr_0_h2.push_front(2);
                     else 
-                        if (op_0[3:0] == 4w3) 
+                        if (hdr.h1.op3[3:0] == 4w3) 
                             hdr_0_h2.push_front(3);
                         else 
-                            if (op_0[3:0] == 4w4) 
+                            if (hdr.h1.op3[3:0] == 4w4) 
                                 hdr_0_h2.push_front(4);
                             else 
-                                if (op_0[3:0] == 4w5) 
+                                if (hdr.h1.op3[3:0] == 4w5) 
                                     hdr_0_h2.push_front(5);
                                 else 
-                                    if (op_0[3:0] == 4w6) 
+                                    if (hdr.h1.op3[3:0] == 4w6) 
                                         hdr_0_h2.push_front(6);
             else 
-                if (op_0[7:4] == 4w2) 
-                    if (op_0[3:0] == 4w1) 
+                if (hdr.h1.op3[7:4] == 4w2) 
+                    if (hdr.h1.op3[3:0] == 4w1) 
                         hdr_0_h2.pop_front(1);
                     else 
-                        if (op_0[3:0] == 4w2) 
+                        if (hdr.h1.op3[3:0] == 4w2) 
                             hdr_0_h2.pop_front(2);
                         else 
-                            if (op_0[3:0] == 4w3) 
+                            if (hdr.h1.op3[3:0] == 4w3) 
                                 hdr_0_h2.pop_front(3);
                             else 
-                                if (op_0[3:0] == 4w4) 
+                                if (hdr.h1.op3[3:0] == 4w4) 
                                     hdr_0_h2.pop_front(4);
                                 else 
-                                    if (op_0[3:0] == 4w5) 
+                                    if (hdr.h1.op3[3:0] == 4w5) 
                                         hdr_0_h2.pop_front(5);
                                     else 
-                                        if (op_0[3:0] == 4w6) 
+                                        if (hdr.h1.op3[3:0] == 4w6) 
                                             hdr_0_h2.pop_front(6);
                 else 
-                    if (op_0[7:4] == 4w3) 
-                        if (op_0[3:0] == 4w0) {
+                    if (hdr.h1.op3[7:4] == 4w3) 
+                        if (hdr.h1.op3[3:0] == 4w0) {
                             hdr_0_h2[0].setValid();
                             hdr_0_h2[0].hdr_type = 8w2;
                             hdr_0_h2[0].f1 = 8w0xa0;
@@ -371,7 +309,7 @@ control cIngress(inout headers hdr, inou
                             hdr_0_h2[0].next_hdr_type = 8w9;
                         }
                         else 
-                            if (op_0[3:0] == 4w1) {
+                            if (hdr.h1.op3[3:0] == 4w1) {
                                 hdr_0_h2[1].setValid();
                                 hdr_0_h2[1].hdr_type = 8w2;
                                 hdr_0_h2[1].f1 = 8w0xa1;
@@ -379,7 +317,7 @@ control cIngress(inout headers hdr, inou
                                 hdr_0_h2[1].next_hdr_type = 8w9;
                             }
                             else 
-                                if (op_0[3:0] == 4w2) {
+                                if (hdr.h1.op3[3:0] == 4w2) {
                                     hdr_0_h2[2].setValid();
                                     hdr_0_h2[2].hdr_type = 8w2;
                                     hdr_0_h2[2].f1 = 8w0xa2;
@@ -387,7 +325,7 @@ control cIngress(inout headers hdr, inou
                                     hdr_0_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
-                                    if (op_0[3:0] == 4w3) {
+                                    if (hdr.h1.op3[3:0] == 4w3) {
                                         hdr_0_h2[3].setValid();
                                         hdr_0_h2[3].hdr_type = 8w2;
                                         hdr_0_h2[3].f1 = 8w0xa3;
@@ -395,7 +333,7 @@ control cIngress(inout headers hdr, inou
                                         hdr_0_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
-                                        if (op_0[3:0] == 4w4) {
+                                        if (hdr.h1.op3[3:0] == 4w4) {
                                             hdr_0_h2[4].setValid();
                                             hdr_0_h2[4].hdr_type = 8w2;
                                             hdr_0_h2[4].f1 = 8w0xa4;
@@ -403,30 +341,23 @@ control cIngress(inout headers hdr, inou
                                             hdr_0_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
-                        if (op_0[7:4] == 4w4) 
-                            if (op_0[3:0] == 4w0) 
+                        if (hdr.h1.op3[7:4] == 4w4) 
+                            if (hdr.h1.op3[3:0] == 4w0) 
                                 hdr_0_h2[0].setInvalid();
                             else 
-                                if (op_0[3:0] == 4w1) 
+                                if (hdr.h1.op3[3:0] == 4w1) 
                                     hdr_0_h2[1].setInvalid();
                                 else 
-                                    if (op_0[3:0] == 4w2) 
+                                    if (hdr.h1.op3[3:0] == 4w2) 
                                         hdr_0_h2[2].setInvalid();
                                     else 
-                                        if (op_0[3:0] == 4w3) 
+                                        if (hdr.h1.op3[3:0] == 4w3) 
                                             hdr_0_h2[3].setInvalid();
                                         else 
-                                            if (op_0[3:0] == 4w4) 
+                                            if (hdr.h1.op3[3:0] == 4w4) 
                                                 hdr_0_h2[4].setInvalid();
         {
-            tmp_3_h1 = hdr_0_h1;
-            tmp_3_h2 = hdr_0_h2;
-            tmp_3_h3 = hdr_0_h3;
-        }
-        {
-            hdr.h1 = tmp_3_h1;
-            hdr.h2 = tmp_3_h2;
-            hdr.h3 = tmp_3_h3;
+            hdr.h2 = hdr_0_h2;
         }
         hdr.h1.h2_valid_bits = 8w0;
         if (hdr.h2[0].isValid()) 
