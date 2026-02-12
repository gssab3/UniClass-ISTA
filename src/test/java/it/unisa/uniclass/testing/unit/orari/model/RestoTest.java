package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Nested;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test d'unità completi per la classe Resto.
 * Verifica costruttori, getter, setter, relazioni JPA e metodi di utilità.
 */
@DisplayName("Test per la classe Resto")
public class RestoTest {

    private Resto resto;

    @BeforeEach
    void setUp() {
        resto = new Resto();
    }

    @Nested
    @DisplayName("Test dei Costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore di default crea un'istanza valida")
        void testCostruttoreDefault() {
            Resto restoTest = new Resto();
            assertNotNull(restoTest);
            assertNull(restoTest.getId());
            assertNull(restoTest.getNome());
            assertNull(restoTest.getCorsoLaurea());
        }

        @Test
        @DisplayName("Costruttore con nome e corso di laurea inizializza correttamente")
        void testCostruttoreConParametri() {
            String nome = "Resto 0";
            CorsoLaurea corsoLaurea = new CorsoLaurea("Ingegneria Informatica");
            Resto restoTest = new Resto(nome, corsoLaurea);

            assertNotNull(restoTest);
            assertEquals(nome, restoTest.getNome());
            assertEquals(corsoLaurea, restoTest.getCorsoLaurea());
        }

        @Test
        @DisplayName("Costruttore con nome null")
        void testCostruttoreConNomeNull() {
            CorsoLaurea corsoLaurea = new CorsoLaurea();
            Resto restoTest = new Resto(null, corsoLaurea);

            assertNotNull(restoTest);
            assertNull(restoTest.getNome());
            assertEquals(corsoLaurea, restoTest.getCorsoLaurea());
        }

        @Test
        @DisplayName("Costruttore con corso di laurea null")
        void testCostruttoreConCorsoLaureNull() {
            String nome = "Resto 1";
            Resto restoTest = new Resto(nome, null);

            assertNotNull(restoTest);
            assertEquals(nome, restoTest.getNome());
            assertNull(restoTest.getCorsoLaurea());
        }

        @Test
        @DisplayName("Costruttore con entrambi i parametri null")
        void testCostruttoreConParametriNull() {
            Resto restoTest = new Resto(null, null);

            assertNotNull(restoTest);
            assertNull(restoTest.getNome());
            assertNull(restoTest.getCorsoLaurea());
        }

        @Test
        @DisplayName("Costruttore con nome vuoto")
        void testCostruttoreConNomeVuoto() {
            CorsoLaurea corsoLaurea = new CorsoLaurea();
            Resto restoTest = new Resto("", corsoLaurea);

            assertNotNull(restoTest);
            assertEquals("", restoTest.getNome());
        }

        @Test
        @DisplayName("Costruttore con nome contenente spazi")
        void testCostruttoreConNomeSpazi() {
            String nome = "Resto Speciale 1 - Turno Pomeridiano";
            CorsoLaurea corsoLaurea = new CorsoLaurea();
            Resto restoTest = new Resto(nome, corsoLaurea);

            assertNotNull(restoTest);
            assertEquals(nome, restoTest.getNome());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'nome'")
    class NomeGetterSetterTest {

        @Test
        @DisplayName("getNome restituisce null per default")
        void testGetNomeDefault() {
            assertNull(resto.getNome());
        }

        @Test
        @DisplayName("setNome e getNome funzionano correttamente")
        void testSetGetNome() {
            String nome = "Resto 2";
            resto.setNome(nome);

            assertEquals(nome, resto.getNome());
        }

        @Test
        @DisplayName("setNome con null è permesso")
        void testSetNomeNull() {
            resto.setNome("Resto Test");
            resto.setNome(null);

            assertNull(resto.getNome());
        }

        @Test
        @DisplayName("setNome con stringa vuota")
        void testSetNomeStringaVuota() {
            resto.setNome("");

            assertEquals("", resto.getNome());
        }

        @Test
        @DisplayName("Modifica sequenziale del nome")
        void testModificaSequenzialaNome() {
            resto.setNome("Resto A");
            assertEquals("Resto A", resto.getNome());

            resto.setNome("Resto B");
            assertEquals("Resto B", resto.getNome());

            resto.setNome("Resto C");
            assertEquals("Resto C", resto.getNome());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'corsoLaurea'")
    class CorsoLaureaGetterSetterTest {

        @Test
        @DisplayName("getCorsoLaurea restituisce null per default")
        void testGetCorsoLaureaDefault() {
            assertNull(resto.getCorsoLaurea());
        }

        @Test
        @DisplayName("setCorsoLaurea e getCorsoLaurea funzionano correttamente")
        void testSetGetCorsoLaurea() {
            CorsoLaurea corsoLaurea = new CorsoLaurea("Ingegneria Gestionale");
            resto.setCorsoLaurea(corsoLaurea);

            assertEquals(corsoLaurea, resto.getCorsoLaurea());
        }

        @Test
        @DisplayName("setCorsoLaurea con null è permesso")
        void testSetCorsoLaureaNull() {
            CorsoLaurea corsoLaurea = new CorsoLaurea();
            resto.setCorsoLaurea(corsoLaurea);
            resto.setCorsoLaurea(null);

            assertNull(resto.getCorsoLaurea());
        }

        @Test
        @DisplayName("Modifica sequenziale del corso di laurea")
        void testModificaSequenzialeCorsoLaurea() {
            CorsoLaurea cl1 = new CorsoLaurea("Corso 1");
            CorsoLaurea cl2 = new CorsoLaurea("Corso 2");
            CorsoLaurea cl3 = new CorsoLaurea("Corso 3");

            resto.setCorsoLaurea(cl1);
            assertEquals(cl1, resto.getCorsoLaurea());

            resto.setCorsoLaurea(cl2);
            assertEquals(cl2, resto.getCorsoLaurea());

            resto.setCorsoLaurea(cl3);
            assertEquals(cl3, resto.getCorsoLaurea());
        }
    }

    @Nested
    @DisplayName("Test del Getter per 'id'")
    class IdGetterTest {

        @Test
        @DisplayName("getId restituisce null per default")
        void testGetIdDefault() {
            assertNull(resto.getId());
        }

        @Test
        @DisplayName("getId dopo costruzione")
        void testGetIdConCostruttore() {
            Resto restoTest = new Resto("Resto Test", new CorsoLaurea());

            assertNull(restoTest.getId());
        }
    }

    @Nested
    @DisplayName("Test di integrazione e scenari complessi")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Creazione completa di un resto con tutte le proprietà")
        void testCreazioneCompleta() {
            CorsoLaurea corsoLaurea = new CorsoLaurea("Ingegneria Civile");
            Resto restoCompleto = new Resto("Resto 0", corsoLaurea);

            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(new Lezione());
            lezioni.add(new Lezione());
            lezioni.add(new Lezione());

            List<Studente> studenti = new ArrayList<>();
            studenti.add(new Studente());
            studenti.add(new Studente());

            assertEquals("Resto 0", restoCompleto.getNome());
            assertEquals(corsoLaurea, restoCompleto.getCorsoLaurea());
        }

        @Test
        @DisplayName("Modifica completa di un resto")
        void testModificaCompleta() {
            resto = new Resto("Iniziale", new CorsoLaurea());

            resto.setNome("Modificato");
            CorsoLaurea nuovoCorso = new CorsoLaurea("Nuovo Corso");
            resto.setCorsoLaurea(nuovoCorso);


            assertEquals("Modificato", resto.getNome());
            assertEquals(nuovoCorso, resto.getCorsoLaurea());
        }

        @Test
        @DisplayName("Reset di tutte le proprietà")
        void testResetProprietà() {
            resto = new Resto("Test", new CorsoLaurea());

            // Reset
            resto.setNome(null);
            resto.setCorsoLaurea(null);

            assertNull(resto.getNome());
            assertNull(resto.getCorsoLaurea());
        }

        @Test
        @DisplayName("Scambio di proprietà tra due resti")
        void testScambioProprietà() {
            Resto resto1 = new Resto("Resto 1", new CorsoLaurea("Corso 1"));
            Resto resto2 = new Resto("Resto 2", new CorsoLaurea("Corso 2"));

            String tempNome = resto1.getNome();
            CorsoLaurea tempCorso = resto1.getCorsoLaurea();

            resto1.setNome(resto2.getNome());
            resto1.setCorsoLaurea(resto2.getCorsoLaurea());

            resto2.setNome(tempNome);
            resto2.setCorsoLaurea(tempCorso);

            assertEquals("Resto 2", resto1.getNome());
            assertEquals("Resto 1", resto2.getNome());
        }

    }

    @Nested
    @DisplayName("Test dei valori limite e casi speciali")
    class CasiLimiteTest {

        @Test
        @DisplayName("Nome resto con caratteri speciali")
        void testNomeConCaratteriSpeciali() {
            String nomeSpeciale = "Resto - Turno (A/B) #1";
            resto.setNome(nomeSpeciale);

            assertEquals(nomeSpeciale, resto.getNome());
        }

        @Test
        @DisplayName("Nome resto con Unicode")
        void testNomeConUnicode() {
            String nomeUnicode = "Resto - ñáéíóú";
            resto.setNome(nomeUnicode);

            assertEquals(nomeUnicode, resto.getNome());
        }

        @Test
        @DisplayName("Nome con stringa molto lunga")
        void testNomeConStringaLunga() {
            String nomeLungo = "R".repeat(1000);
            resto.setNome(nomeLungo);

            assertEquals(nomeLungo, resto.getNome());
            assertEquals(1000, resto.getNome().length());
        }


        @Test
        @DisplayName("Resto con corso di laurea ma senza nome")
        void testRestoSenzaNomeConCorso() {
            CorsoLaurea corso = new CorsoLaurea("Test");
            Resto restoTest = new Resto(null, corso);

            assertNull(restoTest.getNome());
            assertEquals(corso, restoTest.getCorsoLaurea());
        }
    }

    @Nested
    @DisplayName("Test delle Named Queries (verifica costanti)")
    class NamedQueriesTest {

        @Test
        @DisplayName("Verifica costanti Named Queries sono definite")
        void testCostantiNamedQueries() {
            assertEquals("Resto.trovaRestiCorso", Resto.TROVA_RESTI_CORSO);
            assertEquals("Resto.trovaResto", Resto.TROVA_RESTO);
            assertEquals("Resto.trovaRestoNome", Resto.TROVA_RESTO_NOME);
            assertEquals("Resto.trovaRestoNomeCorso", Resto.TROVA_RESTO_NOME_CORSO);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono null")
        void testCostantiNonNull() {
            assertNotNull(Resto.TROVA_RESTI_CORSO);
            assertNotNull(Resto.TROVA_RESTO);
            assertNotNull(Resto.TROVA_RESTO_NOME);
            assertNotNull(Resto.TROVA_RESTO_NOME_CORSO);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono vuote")
        void testCostantiNonVuote() {
            assertFalse(Resto.TROVA_RESTI_CORSO.isEmpty());
            assertFalse(Resto.TROVA_RESTO.isEmpty());
            assertFalse(Resto.TROVA_RESTO_NOME.isEmpty());
            assertFalse(Resto.TROVA_RESTO_NOME_CORSO.isEmpty());
        }
    }
}
