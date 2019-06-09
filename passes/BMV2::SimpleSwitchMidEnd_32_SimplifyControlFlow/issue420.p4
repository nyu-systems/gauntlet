--- before_pass
+++ after_pass
@@ -28,18 +28,8 @@ control cIngress(inout Parsed_packet hdr
     @name(".NoAction") action NoAction_0() {
     }
     @name("cIngress.foo") action foo(bit<16> bar) {
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
     @name("cIngress.tbl1") table tbl1_0 {
         key = {
