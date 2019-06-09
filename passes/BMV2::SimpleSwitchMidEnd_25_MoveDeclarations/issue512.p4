--- before_pass
+++ after_pass
@@ -26,13 +26,15 @@ parser parserI(packet_in pkt, out Parsed
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
     bool hasReturned;
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name("cIngress.foo") action foo() {
         hasReturned = false;
         meta.b = meta.b + 4w5;
         {
-            bool cond;
             {
-                bool pred;
                 cond = meta.b > 4w10;
                 pred = cond;
                 {
@@ -42,9 +44,7 @@ control cIngress(inout Parsed_packet hdr
             }
         }
         {
-            bool cond_0;
             {
-                bool pred_0;
                 cond_0 = !hasReturned;
                 pred_0 = cond_0;
                 meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
