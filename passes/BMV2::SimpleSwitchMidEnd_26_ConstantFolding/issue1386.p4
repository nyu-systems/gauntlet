--- dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:14.492573800 +0200
+++ dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:30:14.494849500 +0200
@@ -39,8 +39,7 @@ control ingress(inout Headers h, inout M
             if (!h.h.isValid()) 
                 c_hasReturned_0 = true;
             if (!c_hasReturned_0) 
-                if (8w0 > 8w0) 
-                    h.h.setValid();
+                ;
         }
         sm.egress_spec = 9w0;
     }
