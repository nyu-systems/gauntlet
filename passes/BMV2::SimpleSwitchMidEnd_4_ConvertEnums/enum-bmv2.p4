--- before_pass
+++ after_pass
@@ -5,10 +5,6 @@ header hdr {
     bit<32> b;
     bit<32> c;
 }
-enum Choice {
-    First,
-    Second
-}
 struct Headers {
     hdr h;
 }
@@ -38,10 +34,10 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    Choice c_c_0;
+    bit<32> c_c_0;
     apply {
-        c_c_0 = Choice.First;
-        if (c_c_0 == Choice.Second) 
+        c_c_0 = 32w0;
+        if (c_c_0 == 32w1) 
             h.h.c = h.h.a;
         else 
             h.h.c = h.h.b;
