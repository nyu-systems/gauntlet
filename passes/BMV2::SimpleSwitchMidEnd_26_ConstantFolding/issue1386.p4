--- dumps/pruned/issue1386-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:00.334182400 +0200
+++ dumps/pruned/issue1386-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:32:00.336052100 +0200
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
