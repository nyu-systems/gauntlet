--- dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:30:53.684941900 +0200
+++ dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:30:53.689129000 +0200
@@ -26,13 +26,15 @@ parser parserI(packet_in pkt, out Parsed
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
     bool hasReturned_0;
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name("cIngress.foo") action foo_0() {
         hasReturned_0 = false;
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
                 cond_0 = !hasReturned_0;
                 pred_0 = cond_0;
                 meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
