package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Nested;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test d'unità completi per la classe CorsoLaurea.
 * Verifica costruttori, getter, setter, relazioni JPA e metodi di utilità.
 */
@DisplayName("Test per la classe CorsoLaurea")
public class CorsoLaureaTest {

    private CorsoLaurea corsoLaurea;

    @BeforeEach
    void setUp() {
        corsoLaurea = new CorsoLaurea();
    }

    @Nested
    @DisplayName("Test dei Costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore di default crea un'istanza valida")
        void testCostruttoreDefault() {
            CorsoLaurea cl = new CorsoLaurea();
            assertNotNull(cl);
            assertNull(cl.getNome());
            assertNull(cl.getId());
            assertNotNull(cl.getCorsi());
            assertNotNull(cl.getResti());
            assertNotNull(cl.getAnniDidattici());
            assertNotNull(cl.getStudenti());
            assertTrue(cl.getCorsi().isEmpty());
            assertTrue(cl.getResti().isEmpty());
            assertTrue(cl.getAnniDidattici().isEmpty());
            assertTrue(cl.getStudenti().isEmpty());
        }

        @Test
        @DisplayName("Costruttore con nome inizializza correttamente")
        void testCostruttoreConNome() {
            String nome = "Ingegneria Informatica";
            CorsoLaurea cl = new CorsoLaurea(nome);

            assertNotNull(cl);
            assertEquals(nome, cl.getNome());
            assertNotNull(cl.getCorsi());
            assertTrue(cl.getCorsi().isEmpty());
        }

        @Test
        @DisplayName("Costruttore con nome null")
        void testCostruttoreConNomeNull() {
            CorsoLaurea cl = new CorsoLaurea(null);

            assertNotNull(cl);
            assertNull(cl.getNome());
            assertNotNull(cl.getCorsi());
        }

        @Test
        @DisplayName("Costruttore con nome vuoto")
        void testCostruttoreConNomeVuoto() {
            CorsoLaurea cl = new CorsoLaurea("");

            assertNotNull(cl);
            assertEquals("", cl.getNome());
        }

        @Test
        @DisplayName("Costruttore con nome contenente spazi")
        void testCostruttoreConNomeSpazi() {
            String nome = "Ingegneria del Software - Triennale";
            CorsoLaurea cl = new CorsoLaurea(nome);

            assertNotNull(cl);
            assertEquals(nome, cl.getNome());
        }

        @Test
        @DisplayName("Costruttore con nome, resti e anni didattici")
        void testCostruttoreConParametriCompleti() {
            String nome = "Ingegneria Civile";
            List<Resto> resti = new ArrayList<>();
            resti.add(new Resto());
            List<AnnoDidattico> anni = new ArrayList<>();
            anni.add(new AnnoDidattico());

            CorsoLaurea cl = new CorsoLaurea(nome, resti, anni);

            assertNotNull(cl);
            assertEquals(nome, cl.getNome());
            assertEquals(resti, cl.getResti());
            assertEquals(anni, cl.getAnniDidattici());
            assertNotNull(cl.getCorsi());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'nome'")
    class NomeGetterSetterTest {

        @Test
        @DisplayName("getNome restituisce null per default")
        void testGetNomeDefault() {
            assertNull(corsoLaurea.getNome());
        }

        @Test
        @DisplayName("setNome e getNome funzionano correttamente")
        void testSetGetNome() {
            String nome = "Ingegneria Gestionale";
            corsoLaurea.setNome(nome);

            assertEquals(nome, corsoLaurea.getNome());
        }

        @Test
        @DisplayName("setNome con null è permesso")
        void testSetNomeNull() {
            corsoLaurea.setNome("Informatica");
            corsoLaurea.setNome(null);

            assertNull(corsoLaurea.getNome());
        }

        @Test
        @DisplayName("setNome con stringa vuota")
        void testSetNomeStringaVuota() {
            corsoLaurea.setNome("");

            assertEquals("", corsoLaurea.getNome());
        }

        @Test
        @DisplayName("Modifica sequenziale del nome")
        void testModificaSequenzialaNome() {
            corsoLaurea.setNome("Corso A");
            assertEquals("Corso A", corsoLaurea.getNome());

            corsoLaurea.setNome("Corso B");
            assertEquals("Corso B", corsoLaurea.getNome());

            corsoLaurea.setNome("Corso C");
            assertEquals("Corso C", corsoLaurea.getNome());
        }
    }

    @Nested
    @DisplayName("Test del Getter per 'id'")
    class IdGetterTest {

        @Test
        @DisplayName("getId restituisce null per default")
        void testGetIdDefault() {
            assertNull(corsoLaurea.getId());
        }

        @Test
        @DisplayName("getId restituisce il valore corretto dopo costruzione")
        void testGetIdConCostruttore() {
            CorsoLaurea cl = new CorsoLaurea("Test");

            assertNull(cl.getId());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'corsi'")
    class CorsiGetterSetterTest {

        @Test
        @DisplayName("getCorsi restituisce lista non null per default")
        void testGetCorsiDefault() {
            List<Corso> corsi = corsoLaurea.getCorsi();

            assertNotNull(corsi);
            assertTrue(corsi.isEmpty());
        }

        @Test
        @DisplayName("setCorsi e getCorsi funzionano correttamente")
        void testSetGetCorsi() {
            List<Corso> corsiNuovi = new ArrayList<>();
            corsiNuovi.add(new Corso("Programmazione"));
            corsiNuovi.add(new Corso("Algoritmi"));

            corsoLaurea.setCorsi(corsiNuovi);

            assertEquals(corsiNuovi, corsoLaurea.getCorsi());
            assertEquals(2, corsoLaurea.getCorsi().size());
        }

        @Test
        @DisplayName("Modifica della lista restituita da getCorsi si riflette sull'oggetto")
        void testModificaListaCorsi() {
            List<Corso> corsi = corsoLaurea.getCorsi();
            Corso nuovoCorso = new Corso("Nuovo Corso");
            corsi.add(nuovoCorso);

            assertEquals(1, corsoLaurea.getCorsi().size());
            assertTrue(corsoLaurea.getCorsi().contains(nuovoCorso));
        }

        @Test
        @DisplayName("Aggiunta multipla di corsi")
        void testAggiuntaMultiplaCorsi() {
            List<Corso> corsi = corsoLaurea.getCorsi();
            for (int i = 0; i < 5; i++) {
                corsi.add(new Corso("Corso " + i));
            }

            assertEquals(5, corsoLaurea.getCorsi().size());
        }

        @Test
        @DisplayName("Rimozione di corsi dalla lista")
        void testRimozionCorsi() {
            List<Corso> corsi = corsoLaurea.getCorsi();
            Corso corso1 = new Corso("Corso 1");
            Corso corso2 = new Corso("Corso 2");
            corsi.add(corso1);
            corsi.add(corso2);

            assertEquals(2, corsoLaurea.getCorsi().size());

            corsi.remove(corso1);

            assertEquals(1, corsoLaurea.getCorsi().size());
            assertTrue(corsoLaurea.getCorsi().contains(corso2));
            assertFalse(corsoLaurea.getCorsi().contains(corso1));
        }

        @Test
        @DisplayName("setCorsi con null")
        void testSetCorsiNull() {
            corsoLaurea.setCorsi(null);

            assertNull(corsoLaurea.getCorsi());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'resti'")
    class RestiGetterSetterTest {

        @Test
        @DisplayName("getResti restituisce lista non null per default")
        void testGetRestiDefault() {
            List<Resto> resti = corsoLaurea.getResti();

            assertNotNull(resti);
            assertTrue(resti.isEmpty());
        }

        @Test
        @DisplayName("setResti e getResti funzionano correttamente")
        void testSetGetResti() {
            List<Resto> restiNuovi = new ArrayList<>();
            restiNuovi.add(new Resto());
            restiNuovi.add(new Resto());

            corsoLaurea.setResti(restiNuovi);

            assertEquals(restiNuovi, corsoLaurea.getResti());
            assertEquals(2, corsoLaurea.getResti().size());
        }

        @Test
        @DisplayName("Modifica della lista restituita da getResti si riflette sull'oggetto")
        void testModificaListaResti() {
            List<Resto> resti = corsoLaurea.getResti();
            Resto nuovoResto = new Resto();
            resti.add(nuovoResto);

            assertEquals(1, corsoLaurea.getResti().size());
            assertTrue(corsoLaurea.getResti().contains(nuovoResto));
        }

        @Test
        @DisplayName("Aggiunta multipla di resti")
        void testAggiuntaMultiplaResti() {
            List<Resto> resti = corsoLaurea.getResti();
            for (int i = 0; i < 3; i++) {
                resti.add(new Resto());
            }

            assertEquals(3, corsoLaurea.getResti().size());
        }

        @Test
        @DisplayName("Rimozione di resti dalla lista")
        void testRimozionResti() {
            List<Resto> resti = corsoLaurea.getResti();
            Resto resto1 = new Resto();
            Resto resto2 = new Resto();
            resti.add(resto1);
            resti.add(resto2);

            assertEquals(2, corsoLaurea.getResti().size());

            resti.remove(resto1);

            assertEquals(1, corsoLaurea.getResti().size());
            assertTrue(corsoLaurea.getResti().contains(resto2));
            assertFalse(corsoLaurea.getResti().contains(resto1));
        }

        @Test
        @DisplayName("setResti con null")
        void testSetRestiNull() {
            corsoLaurea.setResti(null);

            assertNull(corsoLaurea.getResti());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'anniDidattici'")
    class AnniDidatticiGetterSetterTest {

        @Test
        @DisplayName("getAnniDidattici restituisce lista non null per default")
        void testGetAnniDidatticiDefault() {
            List<AnnoDidattico> anni = corsoLaurea.getAnniDidattici();

            assertNotNull(anni);
            assertTrue(anni.isEmpty());
        }

        @Test
        @DisplayName("setAnniDidattici e getAnniDidattici funzionano correttamente")
        void testSetGetAnniDidattici() {
            List<AnnoDidattico> anniNuovi = new ArrayList<>();
            anniNuovi.add(new AnnoDidattico());
            anniNuovi.add(new AnnoDidattico());

            corsoLaurea.setAnniDidattici(anniNuovi);

            assertEquals(anniNuovi, corsoLaurea.getAnniDidattici());
            assertEquals(2, corsoLaurea.getAnniDidattici().size());
        }

        @Test
        @DisplayName("Modifica della lista restituita da getAnniDidattici si riflette sull'oggetto")
        void testModificaListaAnniDidattici() {
            List<AnnoDidattico> anni = corsoLaurea.getAnniDidattici();
            AnnoDidattico nuovoAnno = new AnnoDidattico();
            anni.add(nuovoAnno);

            assertEquals(1, corsoLaurea.getAnniDidattici().size());
            assertTrue(corsoLaurea.getAnniDidattici().contains(nuovoAnno));
        }

        @Test
        @DisplayName("Aggiunta multipla di anni didattici")
        void testAggiuntaMultiplaAnniDidattici() {
            List<AnnoDidattico> anni = corsoLaurea.getAnniDidattici();
            for (int i = 0; i < 4; i++) {
                anni.add(new AnnoDidattico());
            }

            assertEquals(4, corsoLaurea.getAnniDidattici().size());
        }

        @Test
        @DisplayName("Rimozione di anni didattici dalla lista")
        void testRimozionAnniDidattici() {
            List<AnnoDidattico> anni = corsoLaurea.getAnniDidattici();
            AnnoDidattico anno1 = new AnnoDidattico();
            AnnoDidattico anno2 = new AnnoDidattico();
            anni.add(anno1);
            anni.add(anno2);

            assertEquals(2, corsoLaurea.getAnniDidattici().size());

            anni.remove(anno1);

            assertEquals(1, corsoLaurea.getAnniDidattici().size());
            assertTrue(corsoLaurea.getAnniDidattici().contains(anno2));
            assertFalse(corsoLaurea.getAnniDidattici().contains(anno1));
        }

        @Test
        @DisplayName("setAnniDidattici con null")
        void testSetAnniDidatticiNull() {
            corsoLaurea.setAnniDidattici(null);

            assertNull(corsoLaurea.getAnniDidattici());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'studenti'")
    class StudentiGetterSetterTest {

        @Test
        @DisplayName("getStudenti restituisce collection non null per default")
        void testGetStudentiDefault() {
            Collection<Studente> studenti = corsoLaurea.getStudenti();

            assertNotNull(studenti);
            assertTrue(studenti.isEmpty());
        }

        @Test
        @DisplayName("setStudenti e getStudenti funzionano correttamente")
        void testSetGetStudenti() {
            List<Studente> studentiNuovi = new ArrayList<>();
            studentiNuovi.add(new Studente());
            studentiNuovi.add(new Studente());

            corsoLaurea.setStudenti(studentiNuovi);

            assertEquals(studentiNuovi, corsoLaurea.getStudenti());
            assertEquals(2, corsoLaurea.getStudenti().size());
        }

        @Test
        @DisplayName("Modifica della lista restituita da getStudenti si riflette sull'oggetto")
        void testModificaListaStudenti() {
            Collection<Studente> studenti = corsoLaurea.getStudenti();
            if (studenti instanceof List) {
                List<Studente> studentiList = (List<Studente>) studenti;
                Studente nuovoStudente = new Studente();
                studentiList.add(nuovoStudente);

                assertEquals(1, corsoLaurea.getStudenti().size());
                assertTrue(corsoLaurea.getStudenti().contains(nuovoStudente));
            }
        }

        @Test
        @DisplayName("Aggiunta multipla di studenti")
        void testAggiuntaMultiplaStudenti() {
            List<Studente> studentiNuovi = new ArrayList<>();
            for (int i = 0; i < 10; i++) {
                studentiNuovi.add(new Studente());
            }
            corsoLaurea.setStudenti(studentiNuovi);

            assertEquals(10, corsoLaurea.getStudenti().size());
        }

        @Test
        @DisplayName("setStudenti con null")
        void testSetStudentiNull() {
            corsoLaurea.setStudenti(null);

            assertNull(corsoLaurea.getStudenti());
        }
    }

    @Nested
    @DisplayName("Test del metodo toString")
    class ToStringTest {

        @Test
        @DisplayName("toString con valori di default")
        void testToStringDefault() {
            String result = corsoLaurea.toString();

            assertNotNull(result);
            assertTrue(result.contains("CorsoLaurea"));
            assertTrue(result.contains("id="));
            assertTrue(result.contains("nome="));
        }

        @Test
        @DisplayName("toString con nome impostato")
        void testToStringConNome() {
            corsoLaurea.setNome("Ingegneria Informatica");
            String result = corsoLaurea.toString();

            assertNotNull(result);
            assertTrue(result.contains("Ingegneria Informatica"));
        }

        @Test
        @DisplayName("toString con nome null")
        void testToStringConNomeNull() {
            corsoLaurea.setNome(null);
            String result = corsoLaurea.toString();

            assertNotNull(result);
            assertTrue(result.contains("CorsoLaurea"));
        }

        @Test
        @DisplayName("toString non è null o vuoto")
        void testToStringNonVuoto() {
            String result = corsoLaurea.toString();

            assertNotNull(result);
            assertFalse(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test di integrazione e scenari complessi")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Creazione completa di un corso di laurea con tutte le proprietà")
        void testCreazioneCompleta() {
            CorsoLaurea cl = new CorsoLaurea("Ingegneria Industriale");

            List<Corso> corsi = new ArrayList<>();
            corsi.add(new Corso("Corso 1"));
            corsi.add(new Corso("Corso 2"));
            cl.setCorsi(corsi);

            List<Resto> resti = new ArrayList<>();
            resti.add(new Resto());
            cl.setResti(resti);

            List<AnnoDidattico> anni = new ArrayList<>();
            anni.add(new AnnoDidattico());
            cl.setAnniDidattici(anni);

            List<Studente> studenti = new ArrayList<>();
            studenti.add(new Studente());
            cl.setStudenti(studenti);

            assertEquals("Ingegneria Industriale", cl.getNome());
            assertEquals(2, cl.getCorsi().size());
            assertEquals(1, cl.getResti().size());
            assertEquals(1, cl.getAnniDidattici().size());
            assertEquals(1, cl.getStudenti().size());
        }

        @Test
        @DisplayName("Modifica completa di un corso di laurea")
        void testModificaCompleta() {
            corsoLaurea = new CorsoLaurea("Iniziale");

            corsoLaurea.setNome("Modificato");
            corsoLaurea.getCorsi().add(new Corso("Nuovo Corso"));
            corsoLaurea.getResti().add(new Resto());

            assertEquals("Modificato", corsoLaurea.getNome());
            assertEquals(1, corsoLaurea.getCorsi().size());
            assertEquals(1, corsoLaurea.getResti().size());
        }

        @Test
        @DisplayName("Reset di tutte le proprietà")
        void testResetProprietà() {
            corsoLaurea = new CorsoLaurea("Test");
            corsoLaurea.getCorsi().add(new Corso("Corso"));
            corsoLaurea.getResti().add(new Resto());
            corsoLaurea.getAnniDidattici().add(new AnnoDidattico());

            // Reset
            corsoLaurea.setNome(null);
            corsoLaurea.setCorsi(new ArrayList<>());
            corsoLaurea.setResti(new ArrayList<>());
            corsoLaurea.setAnniDidattici(new ArrayList<>());
            corsoLaurea.setStudenti(new ArrayList<>());

            assertNull(corsoLaurea.getNome());
            assertTrue(corsoLaurea.getCorsi().isEmpty());
            assertTrue(corsoLaurea.getResti().isEmpty());
            assertTrue(corsoLaurea.getAnniDidattici().isEmpty());
            assertTrue(corsoLaurea.getStudenti().isEmpty());
        }

        @Test
        @DisplayName("Scambio di proprietà tra due corsi di laurea")
        void testScambioProprietà() {
            CorsoLaurea cl1 = new CorsoLaurea("Corso 1");
            CorsoLaurea cl2 = new CorsoLaurea("Corso 2");

            String tempNome = cl1.getNome();

            cl1.setNome(cl2.getNome());
            cl2.setNome(tempNome);

            assertEquals("Corso 2", cl1.getNome());
            assertEquals("Corso 1", cl2.getNome());
        }

        @Test
        @DisplayName("Associazione multiple corsi, resti, anni e studenti")
        void testAssociazioneMultiple() {
            for (int i = 0; i < 5; i++) {
                corsoLaurea.getCorsi().add(new Corso("Corso " + i));
                corsoLaurea.getResti().add(new Resto());
                corsoLaurea.getAnniDidattici().add(new AnnoDidattico());
            }

            for (int i = 0; i < 20; i++) {
                List<Studente> studenti = new ArrayList<>(corsoLaurea.getStudenti());
                studenti.add(new Studente());
                corsoLaurea.setStudenti(studenti);
            }

            assertEquals(5, corsoLaurea.getCorsi().size());
            assertEquals(5, corsoLaurea.getResti().size());
            assertEquals(5, corsoLaurea.getAnniDidattici().size());
            assertEquals(20, corsoLaurea.getStudenti().size());
        }
    }

    @Nested
    @DisplayName("Test dei valori limite e casi speciali")
    class CasiLimiteTest {

        @Test
        @DisplayName("Nome corso di laurea con caratteri speciali")
        void testNomeConCaratteriSpeciali() {
            String nomeSpeciale = "Ingegneria - Triennale (A/B)";
            corsoLaurea.setNome(nomeSpeciale);

            assertEquals(nomeSpeciale, corsoLaurea.getNome());
        }

        @Test
        @DisplayName("Nome corso di laurea con Unicode")
        void testNomeConUnicode() {
            String nomeUnicode = "Ingegneria - ñáéíóú";
            corsoLaurea.setNome(nomeUnicode);

            assertEquals(nomeUnicode, corsoLaurea.getNome());
        }

        @Test
        @DisplayName("Nome con stringa molto lunga")
        void testNomeConStringaLunga() {
            String nomeLungo = "N".repeat(1000);
            corsoLaurea.setNome(nomeLungo);

            assertEquals(nomeLungo, corsoLaurea.getNome());
            assertEquals(1000, corsoLaurea.getNome().length());
        }

        @Test
        @DisplayName("Lista corsi con molti elementi")
        void testListaCorsiGrande() {
            for (int i = 0; i < 100; i++) {
                corsoLaurea.getCorsi().add(new Corso("Corso " + i));
            }

            assertEquals(100, corsoLaurea.getCorsi().size());
        }

        @Test
        @DisplayName("Lista resti con molti elementi")
        void testListaRestiGrande() {
            for (int i = 0; i < 50; i++) {
                corsoLaurea.getResti().add(new Resto());
            }

            assertEquals(50, corsoLaurea.getResti().size());
        }

        @Test
        @DisplayName("Lista anni didattici con molti elementi")
        void testListaAnniGrande() {
            for (int i = 0; i < 10; i++) {
                corsoLaurea.getAnniDidattici().add(new AnnoDidattico());
            }

            assertEquals(10, corsoLaurea.getAnniDidattici().size());
        }

        @Test
        @DisplayName("Corso di laurea senza nome e senza associazioni")
        void testCorsoLaureaMinimale() {
            CorsoLaurea clMin = new CorsoLaurea();

            assertNull(clMin.getNome());
            assertNull(clMin.getId());
            assertNotNull(clMin.getCorsi());
            assertNotNull(clMin.getResti());
            assertNotNull(clMin.getAnniDidattici());
            assertNotNull(clMin.getStudenti());
        }
    }

    @Nested
    @DisplayName("Test delle Named Queries (verifica costanti)")
    class NamedQueriesTest {

        @Test
        @DisplayName("Verifica costanti Named Queries sono definite")
        void testCostantiNamedQueries() {
            assertEquals("CorsoLaurea.trovaCorsoLaurea", CorsoLaurea.TROVA_CORSOLAUREA);
            assertEquals("CorsoLaurea.trovaTutti", CorsoLaurea.TROVA_TUTTI);
            assertEquals("CorsoLaurea.trovaCorsoLaureaNome", CorsoLaurea.TROVA_CORSOLAUREA_NOME);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono null")
        void testCostantiNonNull() {
            assertNotNull(CorsoLaurea.TROVA_CORSOLAUREA);
            assertNotNull(CorsoLaurea.TROVA_TUTTI);
            assertNotNull(CorsoLaurea.TROVA_CORSOLAUREA_NOME);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono vuote")
        void testCostantiNonVuote() {
            assertFalse(CorsoLaurea.TROVA_CORSOLAUREA.isEmpty());
            assertFalse(CorsoLaurea.TROVA_TUTTI.isEmpty());
            assertFalse(CorsoLaurea.TROVA_CORSOLAUREA_NOME.isEmpty());
        }
    }
}
