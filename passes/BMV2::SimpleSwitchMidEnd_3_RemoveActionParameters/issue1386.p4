--- dumps/pruned/issue1386-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:00.376087600 +0200
+++ dumps/pruned/issue1386-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:00.357717500 +0200
@@ -33,9 +33,10 @@ control deparser(packet_out b, in Header
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     bit<8> c_n_0;
+    bool c_hasReturned_0;
     apply {
         {
-            bool c_hasReturned_0 = false;
+            c_hasReturned_0 = false;
             c_n_0 = 8w0;
             if (!h.h.isValid()) 
                 c_hasReturned_0 = true;
