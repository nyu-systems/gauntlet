*** dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 16:59:43.267739600 +0200
--- dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 16:59:43.270332800 +0200
*************** control pipe(inout Headers_t headers, ou
*** 48,59 ****
      @name("pipe.drop") action drop_0() {
          pass = false;
      }
      @name("pipe.t") table t {
          key = {
!             headers.ipv4.srcAddr + 32w1: exact @name(" headers.ipv4.srcAddr") ;
!             headers.ipv4.dstAddr + 32w1: exact @name("headers.ipv4.dstAddr") ;
!             headers.ethernet.dstAddr   : exact @name("headers.ethernet.dstAddr") ;
!             headers.ethernet.srcAddr   : exact @name("headers.ethernet.srcAddr") ;
          }
          actions = {
              invalidate_0();
--- 48,61 ----
      @name("pipe.drop") action drop_0() {
          pass = false;
      }
+     bit<32> key_0;
+     bit<32> key_1;
      @name("pipe.t") table t {
          key = {
!             key_0                   : exact @name(" headers.ipv4.srcAddr") ;
!             key_1                   : exact @name("headers.ipv4.dstAddr") ;
!             headers.ethernet.dstAddr: exact @name("headers.ethernet.dstAddr") ;
!             headers.ethernet.srcAddr: exact @name("headers.ethernet.srcAddr") ;
          }
          actions = {
              invalidate_0();
*************** control pipe(inout Headers_t headers, ou
*** 63,69 ****
          default_action = drop_0();
      }
      apply {
!         tmp_0 = t.apply().hit;
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
--- 65,75 ----
          default_action = drop_0();
      }
      apply {
!         {
!             key_0 = headers.ipv4.srcAddr + 32w1;
!             key_1 = headers.ipv4.dstAddr + 32w1;
!             tmp_0 = t.apply().hit;
!         }
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
