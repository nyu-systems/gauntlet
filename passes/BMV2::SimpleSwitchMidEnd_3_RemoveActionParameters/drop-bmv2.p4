--- before_pass
+++ after_pass
@@ -10,16 +10,19 @@ parser ParserI(packet_in pk, out H hdr,
     }
 }
 control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
-    @name(".drop") action drop_0(inout standard_metadata_t smeta_1) {
+    standard_metadata_t smeta_1;
+    @name(".drop") action drop_0() {
+        smeta_1 = smeta;
         mark_to_drop(smeta_1);
+        smeta = smeta_1;
     }
     @name("IngressI.forward") table forward_0 {
         key = {
         }
         actions = {
-            drop_0(smeta);
+            drop_0();
         }
-        const default_action = drop_0(smeta);
+        const default_action = drop_0();
     }
     apply {
         forward_0.apply();
