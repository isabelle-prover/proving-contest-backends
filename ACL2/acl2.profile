################################
# acl2 - firejail setup
################################
shell none

private-dev
private-tmp

hostname jails
netfilter
protocol unix,inet,inet6,netlink

noroot
nonewprivs
nosound
nogroups
ipc-namespace
caps.drop all
seccomp

blacklist var

