package it.unisa.uniclass.testing.unit.utenti.service.dao;

import it.unisa.uniclass.utenti.service.dao.DocenteDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.mockito.Mockito.*;

class DocenteDAOTest {

    private EntityManager em;
    private TypedQuery<Docente> docenteQuery;
    private DocenteDAO dao;

    @BeforeEach
    void setUp() {
        em = mock(EntityManager.class);
        docenteQuery = mock(TypedQuery.class);

        dao = new DocenteDAO();

        // Iniettiamo il mock dell'EntityManager via reflection
        try {
            var field = DocenteDAO.class.getDeclaredField("emUniclass");
            field.setAccessible(true);
            field.set(dao, em);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void testTrovaDocenteUniClass() {
        Docente d = new Docente();
        when(em.createNamedQuery(Docente.TROVA_DOCENTE, Docente.class)).thenReturn(docenteQuery);
        when(docenteQuery.setParameter("matricola", "123")).thenReturn(docenteQuery);
        when(docenteQuery.getSingleResult()).thenReturn(d);

        assertEquals(d, dao.trovaDocenteUniClass("123"));
    }

    @Test
    void testTrovaDocenteCorsoLaurea() {
        List<Docente> list = Collections.singletonList(new Docente());
        when(em.createNamedQuery(Docente.TROVA_DOCENTE_CORSOLAUREA, Docente.class)).thenReturn(docenteQuery);
        when(docenteQuery.setParameter("nome", "Ingegneria")).thenReturn(docenteQuery);
        when(docenteQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaDocenteCorsoLaurea("Ingegneria"));
    }

    @Test
    void testTrovaTuttiUniClass() {
        List<Docente> list = Collections.singletonList(new Docente());
        when(em.createNamedQuery(Docente.TROVA_TUTTI, Docente.class)).thenReturn(docenteQuery);
        when(docenteQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaTuttiUniClass());
    }

    @Test
    void testTrovaEmailUniClass() {
        Docente d = new Docente();
        when(em.createNamedQuery(Docente.TROVA_EMAIL, Docente.class)).thenReturn(docenteQuery);
        when(docenteQuery.setParameter("email", "x@y.com")).thenReturn(docenteQuery);
        when(docenteQuery.getSingleResult()).thenReturn(d);

        assertEquals(d, dao.trovaEmailUniClass("x@y.com"));
    }

    @Test
    void testAggiungiDocente() {
        Docente d = new Docente();
        dao.aggiungiDocente(d);
        verify(em).merge(d);
    }

    @Test
    void testRimuoviDocente() {
        Docente d = new Docente();
        dao.rimuoviDocente(d);
        verify(em).remove(d);
    }
}
