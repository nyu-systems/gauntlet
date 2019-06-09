--- before_pass
+++ after_pass
@@ -63,9 +63,17 @@ control cIngress(inout headers hdr, inou
     headers hdr_0;
     bit<8> op_0;
     apply {
-        tmp = hdr;
+        {
+            tmp.h1 = hdr.h1;
+            tmp.h2 = hdr.h2;
+            tmp.h3 = hdr.h3;
+        }
         tmp_0 = hdr.h1.op1;
-        hdr_0 = tmp;
+        {
+            hdr_0.h1 = tmp.h1;
+            hdr_0.h2 = tmp.h2;
+            hdr_0.h3 = tmp.h3;
+        }
         op_0 = tmp_0;
         if (op_0 == 8w0x0) 
             ;
@@ -164,11 +172,27 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (op_0[3:0] == 4w4) 
                                                 hdr_0.h2[4].setInvalid();
-        tmp = hdr_0;
-        hdr = tmp;
-        tmp_1 = hdr;
+        {
+            tmp.h1 = hdr_0.h1;
+            tmp.h2 = hdr_0.h2;
+            tmp.h3 = hdr_0.h3;
+        }
+        {
+            hdr.h1 = tmp.h1;
+            hdr.h2 = tmp.h2;
+            hdr.h3 = tmp.h3;
+        }
+        {
+            tmp_1.h1 = hdr.h1;
+            tmp_1.h2 = hdr.h2;
+            tmp_1.h3 = hdr.h3;
+        }
         tmp_2 = hdr.h1.op2;
-        hdr_0 = tmp_1;
+        {
+            hdr_0.h1 = tmp_1.h1;
+            hdr_0.h2 = tmp_1.h2;
+            hdr_0.h3 = tmp_1.h3;
+        }
         op_0 = tmp_2;
         if (op_0 == 8w0x0) 
             ;
@@ -267,11 +291,27 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (op_0[3:0] == 4w4) 
                                                 hdr_0.h2[4].setInvalid();
-        tmp_1 = hdr_0;
-        hdr = tmp_1;
-        tmp_3 = hdr;
+        {
+            tmp_1.h1 = hdr_0.h1;
+            tmp_1.h2 = hdr_0.h2;
+            tmp_1.h3 = hdr_0.h3;
+        }
+        {
+            hdr.h1 = tmp_1.h1;
+            hdr.h2 = tmp_1.h2;
+            hdr.h3 = tmp_1.h3;
+        }
+        {
+            tmp_3.h1 = hdr.h1;
+            tmp_3.h2 = hdr.h2;
+            tmp_3.h3 = hdr.h3;
+        }
         tmp_4 = hdr.h1.op3;
-        hdr_0 = tmp_3;
+        {
+            hdr_0.h1 = tmp_3.h1;
+            hdr_0.h2 = tmp_3.h2;
+            hdr_0.h3 = tmp_3.h3;
+        }
         op_0 = tmp_4;
         if (op_0 == 8w0x0) 
             ;
@@ -370,8 +410,16 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (op_0[3:0] == 4w4) 
                                                 hdr_0.h2[4].setInvalid();
-        tmp_3 = hdr_0;
-        hdr = tmp_3;
+        {
+            tmp_3.h1 = hdr_0.h1;
+            tmp_3.h2 = hdr_0.h2;
+            tmp_3.h3 = hdr_0.h3;
+        }
+        {
+            hdr.h1 = tmp_3.h1;
+            hdr.h2 = tmp_3.h2;
+            hdr.h3 = tmp_3.h3;
+        }
         hdr.h1.h2_valid_bits = 8w0;
         if (hdr.h2[0].isValid()) 
             hdr.h1.h2_valid_bits[0:0] = 1w1;
