--- dumps/pruned/issue420-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:26.644742400 +0200
+++ dumps/pruned/issue420-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:26.691265400 +0200
@@ -28,18 +28,8 @@ control cIngress(inout Parsed_packet hdr
     @name(".NoAction") action NoAction_0() {
     }
     @name("cIngress.foo") action foo_0(bit<16> bar) {
-        {
-            {
-                {
-                    hdr.ethernet.srcAddr = (bar == 16w0xf00d ? 48w0xdeadbeeff00d : hdr.ethernet.srcAddr);
-                }
-            }
-        }
-        {
-            {
-                hdr.ethernet.srcAddr = (!(bar == 16w0xf00d ? true : false) ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
-            }
-        }
+        hdr.ethernet.srcAddr = (bar == 16w0xf00d ? 48w0xdeadbeeff00d : hdr.ethernet.srcAddr);
+        hdr.ethernet.srcAddr = (!(bar == 16w0xf00d ? true : false) ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
     }
     @name("cIngress.tbl1") table tbl1 {
         key = {
