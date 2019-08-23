--- before_pass
+++ after_pass
@@ -38,9 +38,9 @@ control egress(inout headers hdr, inout
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
+    bool tmp;
     @name(".NoAction") action NoAction_0() {
     }
-    bool tmp;
     @name("ingress.setDest") action setDest() {
         hdr.ethernet.dstAddr = 48w0x6af3400426d3;
     }
