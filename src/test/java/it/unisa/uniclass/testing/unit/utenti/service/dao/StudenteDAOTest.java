package it.unisa.uniclass.testing.unit.utenti.service.dao;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.utenti.service.dao.StudenteDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.mockito.Mockito.*;

class StudenteDAOTest {

    private EntityManager em;
    private TypedQuery<Studente> studenteQuery;
    private StudenteDAO dao;

    @BeforeEach
    void setUp() {
        em = mock(EntityManager.class);
        studenteQuery = mock(TypedQuery.class);

        dao = new StudenteDAO();

        // Iniettiamo il mock dell'EntityManager via reflection
        try {
            var field = StudenteDAO.class.getDeclaredField("emUniClass");
            field.setAccessible(true);
            field.set(dao, em);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void testTrovaStudenteUniClass() {
        Studente s = new Studente();
        when(em.createNamedQuery(Studente.TROVA_STUDENTE, Studente.class)).thenReturn(studenteQuery);
        when(studenteQuery.setParameter("matricola", "123")).thenReturn(studenteQuery);
        when(studenteQuery.getSingleResult()).thenReturn(s);

        assertEquals(s, dao.trovaStudenteUniClass("123"));
    }

    @Test
    void testTrovaStudentiCorso() {
        CorsoLaurea corso = new CorsoLaurea();
        corso.setNome("Ingegneria");
        List<Studente> list = Collections.singletonList(new Studente());

        when(em.createNamedQuery(Studente.TROVA_STUDENTI_CORSO, Studente.class)).thenReturn(studenteQuery);
        when(studenteQuery.setParameter("corso", "Ingegneria")).thenReturn(studenteQuery);
        when(studenteQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaStudentiCorso(corso));
    }

    @Test
    void testTrovaTuttiUniClass() {
        List<Studente> list = Collections.singletonList(new Studente());
        when(em.createNamedQuery(Studente.TROVA_TUTTI, Studente.class)).thenReturn(studenteQuery);
        when(studenteQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaTuttiUniClass());
    }

    @Test
    void testTrovaStudenteEmailUniClass() {
        Studente s = new Studente();
        when(em.createNamedQuery(Studente.TROVA_EMAIL, Studente.class)).thenReturn(studenteQuery);
        when(studenteQuery.setParameter("email", "x@y.com")).thenReturn(studenteQuery);
        when(studenteQuery.getSingleResult()).thenReturn(s);

        assertEquals(s, dao.trovaStudenteEmailUniClass("x@y.com"));
    }

    @Test
    void testAggiungiStudente() {
        Studente s = new Studente();
        dao.aggiungiStudente(s);
        verify(em).merge(s);
    }

    @Test
    void testRimuoviStudente() {
        Studente s = new Studente();
        dao.rimuoviStudente(s);
        verify(em).remove(s);
    }
}
