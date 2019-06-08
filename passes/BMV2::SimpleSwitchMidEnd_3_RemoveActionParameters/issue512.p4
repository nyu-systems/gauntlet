--- dumps/pruned/issue512-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:32.788329000 +0200
+++ dumps/pruned/issue512-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:32.808747500 +0200
@@ -25,8 +25,9 @@ parser parserI(packet_in pkt, out Parsed
     }
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
+    bool hasReturned_0;
     @name("cIngress.foo") action foo_0() {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         meta.b = meta.b + 4w5;
         if (meta.b > 4w10) {
             meta.b = meta.b ^ 4w5;
