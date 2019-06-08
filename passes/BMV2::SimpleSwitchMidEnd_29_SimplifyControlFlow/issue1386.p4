--- dumps/pruned/issue1386-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:00.339568500 +0200
+++ dumps/pruned/issue1386-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:00.341648300 +0200
@@ -34,13 +34,9 @@ control deparser(packet_out b, in Header
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     bool c_hasReturned_0;
     apply {
-        {
-            c_hasReturned_0 = false;
-            if (!h.h.isValid()) 
-                c_hasReturned_0 = true;
-            if (!c_hasReturned_0) 
-                ;
-        }
+        c_hasReturned_0 = false;
+        if (!h.h.isValid()) 
+            c_hasReturned_0 = true;
         sm.egress_spec = 9w0;
     }
 }
