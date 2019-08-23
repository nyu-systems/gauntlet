--- before_pass
+++ after_pass
@@ -9,8 +9,7 @@ header ethernet_t {
     bit<16> etherType;
 }
 struct metadata {
-    @name("meta") 
-    meta_t meta;
+    bit<32> _meta_meter_tag0;
 }
 struct headers {
     @name("ethernet") 
@@ -47,17 +46,17 @@ control ingress(inout headers hdr, inout
             NoAction_0();
         }
         key = {
-            meta.meta.meter_tag: exact @name("meta.meta.meter_tag") ;
+            meta._meta_meter_tag0: exact @name("meta.meta.meter_tag") ;
         }
         size = 16;
         default_action = NoAction_0();
     }
     @name("ingress.m_action") action m_action_0(bit<9> meter_idx) {
         standard_metadata.egress_spec = meter_idx;
-        my_meter.read(meta.meta.meter_tag);
+        my_meter.read(meta._meta_meter_tag0);
     }
     @name("ingress._nop") action _nop_0() {
-        my_meter.read(meta.meta.meter_tag);
+        my_meter.read(meta._meta_meter_tag0);
     }
     @name("ingress.m_table") table m_table_0 {
         actions = {
