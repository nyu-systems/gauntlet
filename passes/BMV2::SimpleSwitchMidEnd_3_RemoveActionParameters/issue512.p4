--- before_pass
+++ after_pass
@@ -25,8 +25,9 @@ parser parserI(packet_in pkt, out Parsed
     }
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
+    bool hasReturned;
     @name("cIngress.foo") action foo() {
-        bool hasReturned = false;
+        hasReturned = false;
         meta.b = meta.b + 4w5;
         if (meta.b > 4w10) {
             meta.b = meta.b ^ 4w5;
