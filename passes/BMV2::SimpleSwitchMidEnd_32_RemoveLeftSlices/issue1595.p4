--- dumps/pruned/issue1595-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:32:06.950263400 +0200
+++ dumps/pruned/issue1595-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-06-08 18:32:06.952415400 +0200
@@ -31,13 +31,13 @@ control cIngress(inout Parsed_packet hdr
         hdr.ethernet.srcAddr = 48w1;
     }
     @name("cIngress.a2") action a2_0() {
-        hdr.ethernet.srcAddr[47:40] = 8w2;
+        hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xff0000000000 | (bit<48>)8w2 << 40 & 48w0xff0000000000;
     }
     @name("cIngress.a3") action a3_0() {
-        hdr.ethernet.srcAddr[47:40] = 8w3;
+        hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xff0000000000 | (bit<48>)8w3 << 40 & 48w0xff0000000000;
     }
     @name("cIngress.a4") action a4_0() {
-        hdr.ethernet.srcAddr[47:40] = 8w4;
+        hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xff0000000000 | (bit<48>)8w4 << 40 & 48w0xff0000000000;
     }
     @name("cIngress.t1") table t1 {
         key = {
@@ -57,16 +57,16 @@ control cIngress(inout Parsed_packet hdr
             a1_0: {
             }
             a2_0: {
-                hdr.ethernet.srcAddr[39:32] = 8w2;
+                hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xff00000000 | (bit<48>)8w2 << 32 & 48w0xff00000000;
             }
             a3_0: {
-                hdr.ethernet.srcAddr[39:32] = 8w3;
+                hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xff00000000 | (bit<48>)8w3 << 32 & 48w0xff00000000;
             }
             a4_0: {
-                hdr.ethernet.srcAddr[39:32] = 8w4;
+                hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xff00000000 | (bit<48>)8w4 << 32 & 48w0xff00000000;
             }
             NoAction_0: {
-                hdr.ethernet.srcAddr[39:32] = 8w5;
+                hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xff00000000 | (bit<48>)8w5 << 32 & 48w0xff00000000;
             }
         }
     }
