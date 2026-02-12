package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.utenti.model.Accademico;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class RestoTest {

    @Test
    @DisplayName("Test Costruttore Vuoto e Setter/Getter")
    void testNoArgsConstructorAndSetters() {
        Resto resto = new Resto();

        Long id = 1L;
        String nome = "Resto 0";
        CorsoLaurea cl = new CorsoLaurea("Informatica");
        List<Lezione> lezioni = new ArrayList<>();
        List<Accademico> accademici = new ArrayList<>();

        resto.setId(id);
        resto.setNome(nome);
        resto.setCorsoLaurea(cl);
        resto.setLezioni(lezioni);
        resto.setAccademici(accademici);

        assertAll(
                () -> assertEquals(id, resto.getId()),
                () -> assertEquals(nome, resto.getNome()),
                () -> assertSame(cl, resto.getCorsoLaurea()),
                () -> assertSame(lezioni, resto.getLezioni()),
                () -> assertSame(accademici, resto.getAccademici())
        );
    }

    @Test
    @DisplayName("Test Costruttore Parametrico")
    void testAllArgsConstructor() {
        String nome = "Resto 1";
        CorsoLaurea cl = new CorsoLaurea("Matematica");

        Resto resto = new Resto(nome, cl);

        assertAll(
                () -> assertEquals(nome, resto.getNome()),
                () -> assertSame(cl, resto.getCorsoLaurea()),
                // Verifica che le liste siano inizializzate (anche se vuote o null di default se non nel costruttore)
                // Nel codice fornito, le liste sono inizializzate alla dichiarazione "new ArrayList<>()"
                () -> assertNotNull(resto.getLezioni()),
                () -> assertNotNull(resto.getAccademici())
        );
    }
}