--- dumps/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:31:33.859200700 +0200
+++ dumps/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:31:33.861040500 +0200
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
