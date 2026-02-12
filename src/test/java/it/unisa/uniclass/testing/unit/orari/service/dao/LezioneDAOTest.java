package it.unisa.uniclass.testing.unit.orari.service.dao;

import it.unisa.uniclass.orari.model.*;
import it.unisa.uniclass.orari.service.dao.LezioneDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Nested;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.sql.Time;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test d'unità per la classe LezioneDAO.
 * Verifica i metodi di recupero, aggiunta e rimozione di lezioni dal database.
 */
@DisplayName("Test per la classe LezioneDAO")
public class LezioneDAOTest {

    @Mock
    private EntityManager emUniClass;

    @Mock
    private TypedQuery<Lezione> typedQueryLezione;

    private LezioneDAO lezioneDAO;
    private Lezione lezione;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);

        lezioneDAO = new LezioneDAO();
        lezioneDAO.emUniClass = emUniClass;

        // Evita loop di circolarità: crea Resto e Corso senza dipendenze circolari
        Resto resto = new Resto();
        resto.setNome("Resto 0");

        lezione = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                            Giorno.LUNEDI, resto, new Corso("Programmazione"),
                            new Aula(1, "Edificio A", "Aula 101"));
    }

    @Nested
    @DisplayName("Test del metodo trovaLezione(long id)")
    class TrovaLezioneByIdTest {

        @Test
        @DisplayName("trovaLezione restituisce lezione per ID valido")
        void testTrovaLezioneById() {
            long id = 1;

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("id", id))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getSingleResult())
                    .thenReturn(lezione);

            Lezione result = lezioneDAO.trovaLezione(id);

            assertNotNull(result);
            assertEquals(1, result.getSemestre());
            verify(emUniClass, times(1)).createNamedQuery(Lezione.TROVA_LEZIONE, Lezione.class);
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniCorso(String nomeCorso)")
    class TrovaLezioniCorsoTest {

        @Test
        @DisplayName("trovaLezioniCorso restituisce lezioni per corso")
        void testTrovaLezioniCorso() {
            String nomeCorso = "Programmazione";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("nomeCorso", nomeCorso))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniCorso(nomeCorso);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(emUniClass, times(1)).createNamedQuery(Lezione.TROVA_LEZIONE_CORSO, Lezione.class);
        }

        @Test
        @DisplayName("trovaLezioniCorso restituisce lista vuota")
        void testTrovaLezioniCorsoVuoto() {
            String nomeCorso = "Corso Inesistente";

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("nomeCorso", nomeCorso))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneDAO.trovaLezioniCorso(nomeCorso);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniOre(Time, Time)")
    class TrovaLezioniOreTest {

        @Test
        @DisplayName("trovaLezioniOre restituisce lezioni per fascia oraria")
        void testTrovaLezioniOre() {
            Time oraInizio = Time.valueOf("09:00:00");
            Time oraFine = Time.valueOf("11:00:00");
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_ORE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("oraInizio", oraInizio))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("oraFine", oraFine))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniOre(oraInizio, oraFine);

            assertNotNull(result);
            assertEquals(1, result.size());
        }

        @Test
        @DisplayName("trovaLezioniOre restituisce lista vuota")
        void testTrovaLezioniOreVuoto() {
            Time oraInizio = Time.valueOf("23:00:00");
            Time oraFine = Time.valueOf("23:30:00");

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_ORE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("oraInizio", oraInizio))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("oraFine", oraFine))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneDAO.trovaLezioniOre(oraInizio, oraFine);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniOreGiorno")
    class TrovaLezioniOreGiornoTest {

        @Test
        @DisplayName("trovaLezioniOreGiorno restituisce lezioni per fascia oraria e giorno")
        void testTrovaLezioniOreGiorno() {
            Time oraInizio = Time.valueOf("09:00:00");
            Time oraFine = Time.valueOf("11:00:00");
            Giorno giorno = Giorno.LUNEDI;
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_ORE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("oraInizio", oraInizio))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("oraFine", oraFine))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("giorno", giorno))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniOreGiorno(oraInizio, oraFine, giorno);

            assertNotNull(result);
            assertEquals(1, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniAule(String nome)")
    class TrovaLezioniAuleTest {

        @Test
        @DisplayName("trovaLezioniAule restituisce lezioni per aula")
        void testTrovaLezioniAule() {
            String nome = "Aula 101";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_AULA, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("nome", nome))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniAule(nome);

            assertNotNull(result);
            assertEquals(1, result.size());
        }

        @Test
        @DisplayName("trovaLezioniAule restituisce lista vuota")
        void testTrovaLezioniAuleVuoto() {
            String nome = "Aula Inesistente";

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_AULA, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("nome", nome))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneDAO.trovaLezioniAule(nome);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTutte()")
    class TrovaTutteTest {

        @Test
        @DisplayName("trovaTutte restituisce lista di tutte le lezioni")
        void testTrovaTutte() {
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            Resto resto2 = new Resto();
            resto2.setNome("Resto 1");
            lezioni.add(new Lezione(2, Time.valueOf("14:00:00"), Time.valueOf("16:00:00"),
                                    Giorno.MARTEDI, resto2, new Corso("Algoritmi"),
                                    new Aula(2, "Edificio B", "Aula 201")));

            when(emUniClass.createNamedQuery(Lezione.TROVA_TUTTE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaTutte();

            assertNotNull(result);
            assertEquals(2, result.size());
        }

        @Test
        @DisplayName("trovaTutte restituisce lista vuota")
        void testTrovaTutteVuoto() {
            when(emUniClass.createNamedQuery(Lezione.TROVA_TUTTE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneDAO.trovaTutte();

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniCorsoLaureaRestoAnno")
    class TrovaLezioniCorsoLaureaRestoAnnoTest {

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnno restituisce lezioni")
        void testTrovaLezioniCorsoLaureaRestoAnno() {
            long clid = 1;
            long reid = 1;
            int anid = 1;
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("corsoLaureaId", clid))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("restoId", reid))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("annoId", anid))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniCorsoLaureaRestoAnno(clid, reid, anid);

            assertNotNull(result);
            assertEquals(1, result.size());
        }

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnno restituisce lista vuota")
        void testTrovaLezioniCorsoLaureaRestoAnnoVuoto() {
            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("corsoLaureaId", 999L))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("restoId", 999L))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("annoId", 999))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneDAO.trovaLezioniCorsoLaureaRestoAnno(999, 999, 999);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniCorsoLaureaRestoAnnoSemestre")
    class TrovaLezioniCorsoLaureaRestoAnnoSemestreTest {

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnnoSemestre restituisce lezioni")
        void testTrovaLezioniCorsoLaureaRestoAnnoSemestre() {
            long clid = 1;
            long reid = 1;
            int anid = 1;
            int semestre = 1;
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("corsoLaureaId", clid))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("restoId", reid))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("annoId", anid))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("semestre", semestre))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniCorsoLaureaRestoAnnoSemestre(clid, reid, anid, semestre);

            assertNotNull(result);
            assertEquals(1, result.size());
        }

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnnoSemestre con semestri diversi")
        void testTrovaLezioniCorsoLaureaRestoAnnoSemestreDiversi() {
            for (int semestre = 1; semestre <= 2; semestre++) {
                when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE, Lezione.class))
                        .thenReturn(typedQueryLezione);
                when(typedQueryLezione.setParameter("corsoLaureaId", 1L))
                        .thenReturn(typedQueryLezione);
                when(typedQueryLezione.setParameter("restoId", 1L))
                        .thenReturn(typedQueryLezione);
                when(typedQueryLezione.setParameter("annoId", 1))
                        .thenReturn(typedQueryLezione);
                when(typedQueryLezione.setParameter("semestre", semestre))
                        .thenReturn(typedQueryLezione);
                when(typedQueryLezione.getResultList())
                        .thenReturn(new ArrayList<>());

                List<Lezione> result = lezioneDAO.trovaLezioniCorsoLaureaRestoAnnoSemestre(1, 1, 1, semestre);

                assertNotNull(result);
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniDocente(String nomeDocente)")
    class TrovaLezioniDocenteTest {

        @Test
        @DisplayName("trovaLezioniDocente restituisce lezioni per docente")
        void testTrovaLezioniDocente() {
            String nomeDocente = "Prof. Rossi";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONI_DOCENTE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("nomeDocente", nomeDocente))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniDocente(nomeDocente);

            assertNotNull(result);
            assertEquals(1, result.size());
        }

        @Test
        @DisplayName("trovaLezioniDocente restituisce lista vuota")
        void testTrovaLezioniDocenteVuoto() {
            String nomeDocente = "Prof. Inesistente";

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONI_DOCENTE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("nomeDocente", nomeDocente))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneDAO.trovaLezioniDocente(nomeDocente);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo aggiungiLezione(Lezione l)")
    class AggiungiLezioneTest {

        @Test
        @DisplayName("aggiungiLezione aggiunge correttamente una lezione")
        void testAggiungiLezione() {
            when(emUniClass.merge(lezione))
                    .thenReturn(lezione);

            lezioneDAO.aggiungiLezione(lezione);

            verify(emUniClass, times(1)).merge(lezione);
        }

        @Test
        @DisplayName("aggiungiLezione aggiunge multiple lezioni")
        void testAggiungiLezioneMultiple() {
            for (int i = 1; i <= 3; i++) {
                Resto resto = new Resto();
                resto.setNome("Resto " + i);
                Lezione lezTest = new Lezione(i, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                                             Giorno.LUNEDI, resto, new Corso("Corso " + i), new Aula());

                when(emUniClass.merge(lezTest))
                        .thenReturn(lezTest);

                lezioneDAO.aggiungiLezione(lezTest);

                verify(emUniClass, times(1)).merge(lezTest);
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo rimuoviLezione(Lezione l)")
    class RimuoviLezioneTest {

        @Test
        @DisplayName("rimuoviLezione rimuove correttamente una lezione")
        void testRimuoviLezione() {
            lezioneDAO.rimuoviLezione(lezione);

            verify(emUniClass, times(1)).remove(lezione);
        }

        @Test
        @DisplayName("rimuoviLezione rimuove multiple lezioni")
        void testRimuoviLezioneMultiple() {
            for (int i = 1; i <= 3; i++) {
                Resto resto = new Resto();
                resto.setNome("Resto " + i);
                Lezione lezTest = new Lezione(i, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                                             Giorno.LUNEDI, resto, new Corso("Corso " + i), new Aula());

                lezioneDAO.rimuoviLezione(lezTest);

                verify(emUniClass, times(1)).remove(lezTest);
            }
        }
    }

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza di operazioni CRUD")
        void testSequenzaCRUD() {
            // Create
            when(emUniClass.merge(lezione))
                    .thenReturn(lezione);
            lezioneDAO.aggiungiLezione(lezione);
            verify(emUniClass, times(1)).merge(lezione);

            // Read
            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("id", 1L))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getSingleResult())
                    .thenReturn(lezione);

            Lezione result = lezioneDAO.trovaLezione(1L);
            assertNotNull(result);

            // Update
            Resto restoModificato = new Resto();
            restoModificato.setNome("Resto Modificato");
            Lezione lezModificata = new Lezione(1, Time.valueOf("10:00:00"), Time.valueOf("12:00:00"),
                                               Giorno.MARTEDI, restoModificato, new Corso(), new Aula());
            when(emUniClass.merge(lezModificata))
                    .thenReturn(lezModificata);
            lezioneDAO.aggiungiLezione(lezModificata);

            // Delete
            lezioneDAO.rimuoviLezione(lezione);
            verify(emUniClass, atLeastOnce()).remove(lezione);
        }

        @Test
        @DisplayName("Ricerca per corso e modifica")
        void testRicercaCorsoEModifica() {
            String nomeCorso = "Programmazione";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO, Lezione.class))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.setParameter("nomeCorso", nomeCorso))
                    .thenReturn(typedQueryLezione);
            when(typedQueryLezione.getResultList())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneDAO.trovaLezioniCorso(nomeCorso);
            assertEquals(1, result.size());

            result.get(0).setSemestre(2);
            when(emUniClass.merge(result.get(0)))
                    .thenReturn(result.get(0));
            lezioneDAO.aggiungiLezione(result.get(0));

            verify(emUniClass, times(1)).merge(result.get(0));
        }
    }
}

