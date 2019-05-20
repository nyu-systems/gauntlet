--- dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:14.499289000 +0200
+++ dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:14.501932100 +0200
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
