--- before_pass
+++ after_pass
@@ -63,9 +63,17 @@ control cIngress(inout headers hdr, inou
     headers hdr_1;
     bit<8> op;
     apply {
-        tmp_5 = hdr;
+        {
+            tmp_5.h1 = hdr.h1;
+            tmp_5.h2 = hdr.h2;
+            tmp_5.h3 = hdr.h3;
+        }
         tmp_6 = hdr.h1.op1;
-        hdr_1 = tmp_5;
+        {
+            hdr_1.h1 = tmp_5.h1;
+            hdr_1.h2 = tmp_5.h2;
+            hdr_1.h3 = tmp_5.h3;
+        }
         op = tmp_6;
         if (op == 8w0x0) 
             ;
@@ -164,11 +172,27 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (op[3:0] == 4w4) 
                                                 hdr_1.h2[4].setInvalid();
-        tmp_5 = hdr_1;
-        hdr = tmp_5;
-        tmp_7 = hdr;
+        {
+            tmp_5.h1 = hdr_1.h1;
+            tmp_5.h2 = hdr_1.h2;
+            tmp_5.h3 = hdr_1.h3;
+        }
+        {
+            hdr.h1 = tmp_5.h1;
+            hdr.h2 = tmp_5.h2;
+            hdr.h3 = tmp_5.h3;
+        }
+        {
+            tmp_7.h1 = hdr.h1;
+            tmp_7.h2 = hdr.h2;
+            tmp_7.h3 = hdr.h3;
+        }
         tmp_8 = hdr.h1.op2;
-        hdr_1 = tmp_7;
+        {
+            hdr_1.h1 = tmp_7.h1;
+            hdr_1.h2 = tmp_7.h2;
+            hdr_1.h3 = tmp_7.h3;
+        }
         op = tmp_8;
         if (op == 8w0x0) 
             ;
@@ -267,11 +291,27 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (op[3:0] == 4w4) 
                                                 hdr_1.h2[4].setInvalid();
-        tmp_7 = hdr_1;
-        hdr = tmp_7;
-        tmp_9 = hdr;
+        {
+            tmp_7.h1 = hdr_1.h1;
+            tmp_7.h2 = hdr_1.h2;
+            tmp_7.h3 = hdr_1.h3;
+        }
+        {
+            hdr.h1 = tmp_7.h1;
+            hdr.h2 = tmp_7.h2;
+            hdr.h3 = tmp_7.h3;
+        }
+        {
+            tmp_9.h1 = hdr.h1;
+            tmp_9.h2 = hdr.h2;
+            tmp_9.h3 = hdr.h3;
+        }
         tmp_10 = hdr.h1.op3;
-        hdr_1 = tmp_9;
+        {
+            hdr_1.h1 = tmp_9.h1;
+            hdr_1.h2 = tmp_9.h2;
+            hdr_1.h3 = tmp_9.h3;
+        }
         op = tmp_10;
         if (op == 8w0x0) 
             ;
@@ -370,8 +410,16 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (op[3:0] == 4w4) 
                                                 hdr_1.h2[4].setInvalid();
-        tmp_9 = hdr_1;
-        hdr = tmp_9;
+        {
+            tmp_9.h1 = hdr_1.h1;
+            tmp_9.h2 = hdr_1.h2;
+            tmp_9.h3 = hdr_1.h3;
+        }
+        {
+            hdr.h1 = tmp_9.h1;
+            hdr.h2 = tmp_9.h2;
+            hdr.h3 = tmp_9.h3;
+        }
         hdr.h1.h2_valid_bits = 8w0;
         if (hdr.h2[0].isValid()) 
             hdr.h1.h2_valid_bits[0:0] = 1w1;
