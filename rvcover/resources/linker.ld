ENTRY(__start)

SECTIONS
{
    . = 0x80000000;

    .text : {
        *(.text)
    }

    /DISCARD/ : {
        *(.note.gnu.build-id)
        *(.comment)
        *(.gnu.version)
        *(.gnu.version_r)
        *(.eh_frame)
        *(.dynamic)
        *(.dynstr)
        *(.dynsym)
        *(.got)
        *(.plt)
        *(.interp)
    }
}