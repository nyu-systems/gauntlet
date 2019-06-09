--- before_pass
+++ after_pass
@@ -54,25 +54,33 @@ parser parserI(packet_in pkt, out header
     }
 }
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
-    headers tmp;
+    h1_t tmp_h1;
+    h2_t[5] tmp_h2;
+    h3_t tmp_h3;
     bit<8> tmp_0;
-    headers tmp_1;
+    h1_t tmp_1_h1;
+    h2_t[5] tmp_1_h2;
+    h3_t tmp_1_h3;
     bit<8> tmp_2;
-    headers tmp_3;
+    h1_t tmp_3_h1;
+    h2_t[5] tmp_3_h2;
+    h3_t tmp_3_h3;
     bit<8> tmp_4;
-    headers hdr_0;
+    h1_t hdr_0_h1;
+    h2_t[5] hdr_0_h2;
+    h3_t hdr_0_h3;
     bit<8> op_0;
     apply {
         {
-            tmp.h1 = hdr.h1;
-            tmp.h2 = hdr.h2;
-            tmp.h3 = hdr.h3;
+            tmp_h1 = hdr.h1;
+            tmp_h2 = hdr.h2;
+            tmp_h3 = hdr.h3;
         }
         tmp_0 = hdr.h1.op1;
         {
-            hdr_0.h1 = tmp.h1;
-            hdr_0.h2 = tmp.h2;
-            hdr_0.h3 = tmp.h3;
+            hdr_0_h1 = tmp_h1;
+            hdr_0_h2 = tmp_h2;
+            hdr_0_h3 = tmp_h3;
         }
         op_0 = tmp_0;
         if (op_0 == 8w0x0) 
@@ -80,118 +88,118 @@ control cIngress(inout headers hdr, inou
         else 
             if (op_0[7:4] == 4w1) 
                 if (op_0[3:0] == 4w1) 
-                    hdr_0.h2.push_front(1);
+                    hdr_0_h2.push_front(1);
                 else 
                     if (op_0[3:0] == 4w2) 
-                        hdr_0.h2.push_front(2);
+                        hdr_0_h2.push_front(2);
                     else 
                         if (op_0[3:0] == 4w3) 
-                            hdr_0.h2.push_front(3);
+                            hdr_0_h2.push_front(3);
                         else 
                             if (op_0[3:0] == 4w4) 
-                                hdr_0.h2.push_front(4);
+                                hdr_0_h2.push_front(4);
                             else 
                                 if (op_0[3:0] == 4w5) 
-                                    hdr_0.h2.push_front(5);
+                                    hdr_0_h2.push_front(5);
                                 else 
                                     if (op_0[3:0] == 4w6) 
-                                        hdr_0.h2.push_front(6);
+                                        hdr_0_h2.push_front(6);
             else 
                 if (op_0[7:4] == 4w2) 
                     if (op_0[3:0] == 4w1) 
-                        hdr_0.h2.pop_front(1);
+                        hdr_0_h2.pop_front(1);
                     else 
                         if (op_0[3:0] == 4w2) 
-                            hdr_0.h2.pop_front(2);
+                            hdr_0_h2.pop_front(2);
                         else 
                             if (op_0[3:0] == 4w3) 
-                                hdr_0.h2.pop_front(3);
+                                hdr_0_h2.pop_front(3);
                             else 
                                 if (op_0[3:0] == 4w4) 
-                                    hdr_0.h2.pop_front(4);
+                                    hdr_0_h2.pop_front(4);
                                 else 
                                     if (op_0[3:0] == 4w5) 
-                                        hdr_0.h2.pop_front(5);
+                                        hdr_0_h2.pop_front(5);
                                     else 
                                         if (op_0[3:0] == 4w6) 
-                                            hdr_0.h2.pop_front(6);
+                                            hdr_0_h2.pop_front(6);
                 else 
                     if (op_0[7:4] == 4w3) 
                         if (op_0[3:0] == 4w0) {
-                            hdr_0.h2[0].setValid();
-                            hdr_0.h2[0].hdr_type = 8w2;
-                            hdr_0.h2[0].f1 = 8w0xa0;
-                            hdr_0.h2[0].f2 = 8w0xa;
-                            hdr_0.h2[0].next_hdr_type = 8w9;
+                            hdr_0_h2[0].setValid();
+                            hdr_0_h2[0].hdr_type = 8w2;
+                            hdr_0_h2[0].f1 = 8w0xa0;
+                            hdr_0_h2[0].f2 = 8w0xa;
+                            hdr_0_h2[0].next_hdr_type = 8w9;
                         }
                         else 
                             if (op_0[3:0] == 4w1) {
-                                hdr_0.h2[1].setValid();
-                                hdr_0.h2[1].hdr_type = 8w2;
-                                hdr_0.h2[1].f1 = 8w0xa1;
-                                hdr_0.h2[1].f2 = 8w0x1a;
-                                hdr_0.h2[1].next_hdr_type = 8w9;
+                                hdr_0_h2[1].setValid();
+                                hdr_0_h2[1].hdr_type = 8w2;
+                                hdr_0_h2[1].f1 = 8w0xa1;
+                                hdr_0_h2[1].f2 = 8w0x1a;
+                                hdr_0_h2[1].next_hdr_type = 8w9;
                             }
                             else 
                                 if (op_0[3:0] == 4w2) {
-                                    hdr_0.h2[2].setValid();
-                                    hdr_0.h2[2].hdr_type = 8w2;
-                                    hdr_0.h2[2].f1 = 8w0xa2;
-                                    hdr_0.h2[2].f2 = 8w0x2a;
-                                    hdr_0.h2[2].next_hdr_type = 8w9;
+                                    hdr_0_h2[2].setValid();
+                                    hdr_0_h2[2].hdr_type = 8w2;
+                                    hdr_0_h2[2].f1 = 8w0xa2;
+                                    hdr_0_h2[2].f2 = 8w0x2a;
+                                    hdr_0_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
                                     if (op_0[3:0] == 4w3) {
-                                        hdr_0.h2[3].setValid();
-                                        hdr_0.h2[3].hdr_type = 8w2;
-                                        hdr_0.h2[3].f1 = 8w0xa3;
-                                        hdr_0.h2[3].f2 = 8w0x3a;
-                                        hdr_0.h2[3].next_hdr_type = 8w9;
+                                        hdr_0_h2[3].setValid();
+                                        hdr_0_h2[3].hdr_type = 8w2;
+                                        hdr_0_h2[3].f1 = 8w0xa3;
+                                        hdr_0_h2[3].f2 = 8w0x3a;
+                                        hdr_0_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
                                         if (op_0[3:0] == 4w4) {
-                                            hdr_0.h2[4].setValid();
-                                            hdr_0.h2[4].hdr_type = 8w2;
-                                            hdr_0.h2[4].f1 = 8w0xa4;
-                                            hdr_0.h2[4].f2 = 8w0x4a;
-                                            hdr_0.h2[4].next_hdr_type = 8w9;
+                                            hdr_0_h2[4].setValid();
+                                            hdr_0_h2[4].hdr_type = 8w2;
+                                            hdr_0_h2[4].f1 = 8w0xa4;
+                                            hdr_0_h2[4].f2 = 8w0x4a;
+                                            hdr_0_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
                         if (op_0[7:4] == 4w4) 
                             if (op_0[3:0] == 4w0) 
-                                hdr_0.h2[0].setInvalid();
+                                hdr_0_h2[0].setInvalid();
                             else 
                                 if (op_0[3:0] == 4w1) 
-                                    hdr_0.h2[1].setInvalid();
+                                    hdr_0_h2[1].setInvalid();
                                 else 
                                     if (op_0[3:0] == 4w2) 
-                                        hdr_0.h2[2].setInvalid();
+                                        hdr_0_h2[2].setInvalid();
                                     else 
                                         if (op_0[3:0] == 4w3) 
-                                            hdr_0.h2[3].setInvalid();
+                                            hdr_0_h2[3].setInvalid();
                                         else 
                                             if (op_0[3:0] == 4w4) 
-                                                hdr_0.h2[4].setInvalid();
+                                                hdr_0_h2[4].setInvalid();
         {
-            tmp.h1 = hdr_0.h1;
-            tmp.h2 = hdr_0.h2;
-            tmp.h3 = hdr_0.h3;
+            tmp_h1 = hdr_0_h1;
+            tmp_h2 = hdr_0_h2;
+            tmp_h3 = hdr_0_h3;
         }
         {
-            hdr.h1 = tmp.h1;
-            hdr.h2 = tmp.h2;
-            hdr.h3 = tmp.h3;
+            hdr.h1 = tmp_h1;
+            hdr.h2 = tmp_h2;
+            hdr.h3 = tmp_h3;
         }
         {
-            tmp_1.h1 = hdr.h1;
-            tmp_1.h2 = hdr.h2;
-            tmp_1.h3 = hdr.h3;
+            tmp_1_h1 = hdr.h1;
+            tmp_1_h2 = hdr.h2;
+            tmp_1_h3 = hdr.h3;
         }
         tmp_2 = hdr.h1.op2;
         {
-            hdr_0.h1 = tmp_1.h1;
-            hdr_0.h2 = tmp_1.h2;
-            hdr_0.h3 = tmp_1.h3;
+            hdr_0_h1 = tmp_1_h1;
+            hdr_0_h2 = tmp_1_h2;
+            hdr_0_h3 = tmp_1_h3;
         }
         op_0 = tmp_2;
         if (op_0 == 8w0x0) 
@@ -199,118 +207,118 @@ control cIngress(inout headers hdr, inou
         else 
             if (op_0[7:4] == 4w1) 
                 if (op_0[3:0] == 4w1) 
-                    hdr_0.h2.push_front(1);
+                    hdr_0_h2.push_front(1);
                 else 
                     if (op_0[3:0] == 4w2) 
-                        hdr_0.h2.push_front(2);
+                        hdr_0_h2.push_front(2);
                     else 
                         if (op_0[3:0] == 4w3) 
-                            hdr_0.h2.push_front(3);
+                            hdr_0_h2.push_front(3);
                         else 
                             if (op_0[3:0] == 4w4) 
-                                hdr_0.h2.push_front(4);
+                                hdr_0_h2.push_front(4);
                             else 
                                 if (op_0[3:0] == 4w5) 
-                                    hdr_0.h2.push_front(5);
+                                    hdr_0_h2.push_front(5);
                                 else 
                                     if (op_0[3:0] == 4w6) 
-                                        hdr_0.h2.push_front(6);
+                                        hdr_0_h2.push_front(6);
             else 
                 if (op_0[7:4] == 4w2) 
                     if (op_0[3:0] == 4w1) 
-                        hdr_0.h2.pop_front(1);
+                        hdr_0_h2.pop_front(1);
                     else 
                         if (op_0[3:0] == 4w2) 
-                            hdr_0.h2.pop_front(2);
+                            hdr_0_h2.pop_front(2);
                         else 
                             if (op_0[3:0] == 4w3) 
-                                hdr_0.h2.pop_front(3);
+                                hdr_0_h2.pop_front(3);
                             else 
                                 if (op_0[3:0] == 4w4) 
-                                    hdr_0.h2.pop_front(4);
+                                    hdr_0_h2.pop_front(4);
                                 else 
                                     if (op_0[3:0] == 4w5) 
-                                        hdr_0.h2.pop_front(5);
+                                        hdr_0_h2.pop_front(5);
                                     else 
                                         if (op_0[3:0] == 4w6) 
-                                            hdr_0.h2.pop_front(6);
+                                            hdr_0_h2.pop_front(6);
                 else 
                     if (op_0[7:4] == 4w3) 
                         if (op_0[3:0] == 4w0) {
-                            hdr_0.h2[0].setValid();
-                            hdr_0.h2[0].hdr_type = 8w2;
-                            hdr_0.h2[0].f1 = 8w0xa0;
-                            hdr_0.h2[0].f2 = 8w0xa;
-                            hdr_0.h2[0].next_hdr_type = 8w9;
+                            hdr_0_h2[0].setValid();
+                            hdr_0_h2[0].hdr_type = 8w2;
+                            hdr_0_h2[0].f1 = 8w0xa0;
+                            hdr_0_h2[0].f2 = 8w0xa;
+                            hdr_0_h2[0].next_hdr_type = 8w9;
                         }
                         else 
                             if (op_0[3:0] == 4w1) {
-                                hdr_0.h2[1].setValid();
-                                hdr_0.h2[1].hdr_type = 8w2;
-                                hdr_0.h2[1].f1 = 8w0xa1;
-                                hdr_0.h2[1].f2 = 8w0x1a;
-                                hdr_0.h2[1].next_hdr_type = 8w9;
+                                hdr_0_h2[1].setValid();
+                                hdr_0_h2[1].hdr_type = 8w2;
+                                hdr_0_h2[1].f1 = 8w0xa1;
+                                hdr_0_h2[1].f2 = 8w0x1a;
+                                hdr_0_h2[1].next_hdr_type = 8w9;
                             }
                             else 
                                 if (op_0[3:0] == 4w2) {
-                                    hdr_0.h2[2].setValid();
-                                    hdr_0.h2[2].hdr_type = 8w2;
-                                    hdr_0.h2[2].f1 = 8w0xa2;
-                                    hdr_0.h2[2].f2 = 8w0x2a;
-                                    hdr_0.h2[2].next_hdr_type = 8w9;
+                                    hdr_0_h2[2].setValid();
+                                    hdr_0_h2[2].hdr_type = 8w2;
+                                    hdr_0_h2[2].f1 = 8w0xa2;
+                                    hdr_0_h2[2].f2 = 8w0x2a;
+                                    hdr_0_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
                                     if (op_0[3:0] == 4w3) {
-                                        hdr_0.h2[3].setValid();
-                                        hdr_0.h2[3].hdr_type = 8w2;
-                                        hdr_0.h2[3].f1 = 8w0xa3;
-                                        hdr_0.h2[3].f2 = 8w0x3a;
-                                        hdr_0.h2[3].next_hdr_type = 8w9;
+                                        hdr_0_h2[3].setValid();
+                                        hdr_0_h2[3].hdr_type = 8w2;
+                                        hdr_0_h2[3].f1 = 8w0xa3;
+                                        hdr_0_h2[3].f2 = 8w0x3a;
+                                        hdr_0_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
                                         if (op_0[3:0] == 4w4) {
-                                            hdr_0.h2[4].setValid();
-                                            hdr_0.h2[4].hdr_type = 8w2;
-                                            hdr_0.h2[4].f1 = 8w0xa4;
-                                            hdr_0.h2[4].f2 = 8w0x4a;
-                                            hdr_0.h2[4].next_hdr_type = 8w9;
+                                            hdr_0_h2[4].setValid();
+                                            hdr_0_h2[4].hdr_type = 8w2;
+                                            hdr_0_h2[4].f1 = 8w0xa4;
+                                            hdr_0_h2[4].f2 = 8w0x4a;
+                                            hdr_0_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
                         if (op_0[7:4] == 4w4) 
                             if (op_0[3:0] == 4w0) 
-                                hdr_0.h2[0].setInvalid();
+                                hdr_0_h2[0].setInvalid();
                             else 
                                 if (op_0[3:0] == 4w1) 
-                                    hdr_0.h2[1].setInvalid();
+                                    hdr_0_h2[1].setInvalid();
                                 else 
                                     if (op_0[3:0] == 4w2) 
-                                        hdr_0.h2[2].setInvalid();
+                                        hdr_0_h2[2].setInvalid();
                                     else 
                                         if (op_0[3:0] == 4w3) 
-                                            hdr_0.h2[3].setInvalid();
+                                            hdr_0_h2[3].setInvalid();
                                         else 
                                             if (op_0[3:0] == 4w4) 
-                                                hdr_0.h2[4].setInvalid();
+                                                hdr_0_h2[4].setInvalid();
         {
-            tmp_1.h1 = hdr_0.h1;
-            tmp_1.h2 = hdr_0.h2;
-            tmp_1.h3 = hdr_0.h3;
+            tmp_1_h1 = hdr_0_h1;
+            tmp_1_h2 = hdr_0_h2;
+            tmp_1_h3 = hdr_0_h3;
         }
         {
-            hdr.h1 = tmp_1.h1;
-            hdr.h2 = tmp_1.h2;
-            hdr.h3 = tmp_1.h3;
+            hdr.h1 = tmp_1_h1;
+            hdr.h2 = tmp_1_h2;
+            hdr.h3 = tmp_1_h3;
         }
         {
-            tmp_3.h1 = hdr.h1;
-            tmp_3.h2 = hdr.h2;
-            tmp_3.h3 = hdr.h3;
+            tmp_3_h1 = hdr.h1;
+            tmp_3_h2 = hdr.h2;
+            tmp_3_h3 = hdr.h3;
         }
         tmp_4 = hdr.h1.op3;
         {
-            hdr_0.h1 = tmp_3.h1;
-            hdr_0.h2 = tmp_3.h2;
-            hdr_0.h3 = tmp_3.h3;
+            hdr_0_h1 = tmp_3_h1;
+            hdr_0_h2 = tmp_3_h2;
+            hdr_0_h3 = tmp_3_h3;
         }
         op_0 = tmp_4;
         if (op_0 == 8w0x0) 
@@ -318,107 +326,107 @@ control cIngress(inout headers hdr, inou
         else 
             if (op_0[7:4] == 4w1) 
                 if (op_0[3:0] == 4w1) 
-                    hdr_0.h2.push_front(1);
+                    hdr_0_h2.push_front(1);
                 else 
                     if (op_0[3:0] == 4w2) 
-                        hdr_0.h2.push_front(2);
+                        hdr_0_h2.push_front(2);
                     else 
                         if (op_0[3:0] == 4w3) 
-                            hdr_0.h2.push_front(3);
+                            hdr_0_h2.push_front(3);
                         else 
                             if (op_0[3:0] == 4w4) 
-                                hdr_0.h2.push_front(4);
+                                hdr_0_h2.push_front(4);
                             else 
                                 if (op_0[3:0] == 4w5) 
-                                    hdr_0.h2.push_front(5);
+                                    hdr_0_h2.push_front(5);
                                 else 
                                     if (op_0[3:0] == 4w6) 
-                                        hdr_0.h2.push_front(6);
+                                        hdr_0_h2.push_front(6);
             else 
                 if (op_0[7:4] == 4w2) 
                     if (op_0[3:0] == 4w1) 
-                        hdr_0.h2.pop_front(1);
+                        hdr_0_h2.pop_front(1);
                     else 
                         if (op_0[3:0] == 4w2) 
-                            hdr_0.h2.pop_front(2);
+                            hdr_0_h2.pop_front(2);
                         else 
                             if (op_0[3:0] == 4w3) 
-                                hdr_0.h2.pop_front(3);
+                                hdr_0_h2.pop_front(3);
                             else 
                                 if (op_0[3:0] == 4w4) 
-                                    hdr_0.h2.pop_front(4);
+                                    hdr_0_h2.pop_front(4);
                                 else 
                                     if (op_0[3:0] == 4w5) 
-                                        hdr_0.h2.pop_front(5);
+                                        hdr_0_h2.pop_front(5);
                                     else 
                                         if (op_0[3:0] == 4w6) 
-                                            hdr_0.h2.pop_front(6);
+                                            hdr_0_h2.pop_front(6);
                 else 
                     if (op_0[7:4] == 4w3) 
                         if (op_0[3:0] == 4w0) {
-                            hdr_0.h2[0].setValid();
-                            hdr_0.h2[0].hdr_type = 8w2;
-                            hdr_0.h2[0].f1 = 8w0xa0;
-                            hdr_0.h2[0].f2 = 8w0xa;
-                            hdr_0.h2[0].next_hdr_type = 8w9;
+                            hdr_0_h2[0].setValid();
+                            hdr_0_h2[0].hdr_type = 8w2;
+                            hdr_0_h2[0].f1 = 8w0xa0;
+                            hdr_0_h2[0].f2 = 8w0xa;
+                            hdr_0_h2[0].next_hdr_type = 8w9;
                         }
                         else 
                             if (op_0[3:0] == 4w1) {
-                                hdr_0.h2[1].setValid();
-                                hdr_0.h2[1].hdr_type = 8w2;
-                                hdr_0.h2[1].f1 = 8w0xa1;
-                                hdr_0.h2[1].f2 = 8w0x1a;
-                                hdr_0.h2[1].next_hdr_type = 8w9;
+                                hdr_0_h2[1].setValid();
+                                hdr_0_h2[1].hdr_type = 8w2;
+                                hdr_0_h2[1].f1 = 8w0xa1;
+                                hdr_0_h2[1].f2 = 8w0x1a;
+                                hdr_0_h2[1].next_hdr_type = 8w9;
                             }
                             else 
                                 if (op_0[3:0] == 4w2) {
-                                    hdr_0.h2[2].setValid();
-                                    hdr_0.h2[2].hdr_type = 8w2;
-                                    hdr_0.h2[2].f1 = 8w0xa2;
-                                    hdr_0.h2[2].f2 = 8w0x2a;
-                                    hdr_0.h2[2].next_hdr_type = 8w9;
+                                    hdr_0_h2[2].setValid();
+                                    hdr_0_h2[2].hdr_type = 8w2;
+                                    hdr_0_h2[2].f1 = 8w0xa2;
+                                    hdr_0_h2[2].f2 = 8w0x2a;
+                                    hdr_0_h2[2].next_hdr_type = 8w9;
                                 }
                                 else 
                                     if (op_0[3:0] == 4w3) {
-                                        hdr_0.h2[3].setValid();
-                                        hdr_0.h2[3].hdr_type = 8w2;
-                                        hdr_0.h2[3].f1 = 8w0xa3;
-                                        hdr_0.h2[3].f2 = 8w0x3a;
-                                        hdr_0.h2[3].next_hdr_type = 8w9;
+                                        hdr_0_h2[3].setValid();
+                                        hdr_0_h2[3].hdr_type = 8w2;
+                                        hdr_0_h2[3].f1 = 8w0xa3;
+                                        hdr_0_h2[3].f2 = 8w0x3a;
+                                        hdr_0_h2[3].next_hdr_type = 8w9;
                                     }
                                     else 
                                         if (op_0[3:0] == 4w4) {
-                                            hdr_0.h2[4].setValid();
-                                            hdr_0.h2[4].hdr_type = 8w2;
-                                            hdr_0.h2[4].f1 = 8w0xa4;
-                                            hdr_0.h2[4].f2 = 8w0x4a;
-                                            hdr_0.h2[4].next_hdr_type = 8w9;
+                                            hdr_0_h2[4].setValid();
+                                            hdr_0_h2[4].hdr_type = 8w2;
+                                            hdr_0_h2[4].f1 = 8w0xa4;
+                                            hdr_0_h2[4].f2 = 8w0x4a;
+                                            hdr_0_h2[4].next_hdr_type = 8w9;
                                         }
                     else 
                         if (op_0[7:4] == 4w4) 
                             if (op_0[3:0] == 4w0) 
-                                hdr_0.h2[0].setInvalid();
+                                hdr_0_h2[0].setInvalid();
                             else 
                                 if (op_0[3:0] == 4w1) 
-                                    hdr_0.h2[1].setInvalid();
+                                    hdr_0_h2[1].setInvalid();
                                 else 
                                     if (op_0[3:0] == 4w2) 
-                                        hdr_0.h2[2].setInvalid();
+                                        hdr_0_h2[2].setInvalid();
                                     else 
                                         if (op_0[3:0] == 4w3) 
-                                            hdr_0.h2[3].setInvalid();
+                                            hdr_0_h2[3].setInvalid();
                                         else 
                                             if (op_0[3:0] == 4w4) 
-                                                hdr_0.h2[4].setInvalid();
+                                                hdr_0_h2[4].setInvalid();
         {
-            tmp_3.h1 = hdr_0.h1;
-            tmp_3.h2 = hdr_0.h2;
-            tmp_3.h3 = hdr_0.h3;
+            tmp_3_h1 = hdr_0_h1;
+            tmp_3_h2 = hdr_0_h2;
+            tmp_3_h3 = hdr_0_h3;
         }
         {
-            hdr.h1 = tmp_3.h1;
-            hdr.h2 = tmp_3.h2;
-            hdr.h3 = tmp_3.h3;
+            hdr.h1 = tmp_3_h1;
+            hdr.h2 = tmp_3_h2;
+            hdr.h3 = tmp_3_h3;
         }
         hdr.h1.h2_valid_bits = 8w0;
         if (hdr.h2[0].isValid()) 
