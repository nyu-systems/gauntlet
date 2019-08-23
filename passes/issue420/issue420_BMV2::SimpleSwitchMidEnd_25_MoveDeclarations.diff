--- before_pass
+++ after_pass
@@ -27,14 +27,16 @@ parser parserI(packet_in pkt, out Parsed
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
     bool hasReturned;
     bool hasReturned_0;
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("cIngress.foo") action foo(bit<16> bar) {
         hasReturned = false;
         {
-            bool cond;
             {
-                bool pred;
                 cond = bar == 16w0xf00d;
                 pred = cond;
                 {
@@ -44,9 +46,7 @@ control cIngress(inout Parsed_packet hdr
             }
         }
         {
-            bool cond_0;
             {
-                bool pred_0;
                 cond_0 = !hasReturned;
                 pred_0 = cond_0;
                 hdr.ethernet.srcAddr = (pred_0 ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
